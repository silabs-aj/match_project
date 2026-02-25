{-# LANGUAGE ScopedTypeVariables #-}


import Data.Time.Clock
import System.Environment (getArgs)
import System.FilePath (takeExtension)

import Criterion.Main
import Control.Monad (when)
import qualified Codec.Compression.GZip as GZip
import qualified Data.ByteString as BS
import qualified Data.ByteString.Char8 as B8
import qualified Data.ByteString.Lazy as BL
import qualified Data.ByteString.Lazy.Char8 as BL8

import Data.Char (isDigit, isSpace, toUpper)
import Data.List (find, partition, isPrefixOf)

import qualified Data.Vector.Unboxed as U
import qualified Data.Vector.Unboxed.Mutable as M
import Data.Word (Word8)

--data Rep a = Null | Node [a] (Rep a) (Rep a) deriving (Show)

{-
match   ws  =   map fst . filter (ok . snd) . scanl step (0,root)
    where   
            step    (n,t) x  =   (n+1,op' t x)

            ok  (Node vs l r)   =   (null vs)
        
            op'     Null    x           =   root
            op'     (Node [] l r)   x   =   op' l  x 
            op'     (Node (v:vs) l r) x   
                    |x == v             =   r
                    |otherwise          =   op' l x

            grep    l   []      =   Node [] l   Null
            grep    l   (v:vs)    =   Node (v:vs) l (grep (op' l v) vs)

            root    =   grep Null   ws
-}
----------------------------------------------------------------------------

-- Utilities

-- Generate a Vector from a ByteString without an intermediate list
toVecBS :: BS.ByteString -> U.Vector Word8
toVecBS bs = U.generate (BS.length bs) (BS.index bs)

-- Keep only DNA letters and uppercase them (ACGTN). (Used by full-file loader)
cleanDNA :: BS.ByteString -> BS.ByteString
cleanDNA =
  B8.map toUpper . B8.filter isDNA
  where
    isDNA c = c `elem` ("ACGTNacgtn" :: String)

-- For the streaming ROI loader we *preserve length*: non-ACGTN -> 'N'
normalizeDNAChar :: Char -> Char
normalizeDNAChar c =
  case toUpper c of
    'A' -> 'A'; 'C' -> 'C'; 'G' -> 'G'; 'T' -> 'T'; 'N' -> 'N'
    _   -> 'N'

--------------------------------------------------------------------------------
-- KMP (Vector) for all match positions (overlapping)

-- Build the LPS (longest proper prefix which is also a suffix) table.
buildLPS :: U.Vector Word8 -> U.Vector Int
buildLPS pat = U.create $ do
  let m = U.length pat
  lps <- M.replicate m 0
  let loop !len !i
        | i >= m = pure lps
        | pat U.! i == pat U.! len = do
            M.write lps i (len + 1)
            loop (len + 1) (i + 1)
        | len /= 0 = do
            len' <- M.read lps (len - 1)
            loop len' i
        | otherwise = do
            M.write lps i 0
            loop 0 (i + 1)
  if m <= 1 then pure lps else loop 0 1

-- Return ALL match positions (0-based, overlapping) of pat in txt.
kmpSearchAll :: U.Vector Word8 -> U.Vector Int -> U.Vector Word8 -> [Int]
kmpSearchAll pat lps txt
  | m == 0    = [0 .. n]
  | otherwise = go 0 0 []
  where
    n = U.length txt
    m = U.length pat
    go !i !j acc
      | i >= n = reverse acc
      | txt U.! i == pat U.! j =
          if j == m - 1
             then go (i + 1) (lps U.! j) ((i - m + 1) : acc)
             else go (i + 1) (j + 1) acc
      | j /= 0  = go i (lps U.! (j - 1)) acc
      | otherwise = go (i + 1) 0 acc

--------------------------------------------------------------------------------
-- Your KMP (Rep automaton) – *without* the unused `us`

-- States only keep the remaining suffix `vs`; transitions are failure `l` and
-- success `r`. A state is accepting iff `vs` is empty.
data Rep = RNull | RNode !BS.ByteString Rep Rep
  deriving (Show)

-- Build the automaton root for a pattern
buildRep :: BS.ByteString -> Rep
buildRep pat = root
  where
    root = grep RNull pat

    -- Single-step transition (closed over 'root')
    stepOp :: Rep -> Word8 -> Rep
    stepOp RNull _ = root
    stepOp (RNode vs l r) x
      | BS.null vs       = stepOp l x
      | BS.head vs == x  = r
      | otherwise        = stepOp l x

    -- Build a node and its 'r' transition
    grep :: Rep -> BS.ByteString -> Rep
    grep l vs
      | BS.null vs = RNode BS.empty l RNull
      | otherwise  =
          let v   = BS.head vs
              vs' = BS.tail vs
              l'  = stepOp l v
              r'  = grep l' vs'
          in RNode vs (next l v) r'
--          in RNode vs l r'

    next :: Rep -> Word8 -> Rep
    next RNull _ = RNull
    next t@(RNode vs l _) x =
      case BS.uncons vs of
        Nothing       -> t
        Just (v, _)
          | v == x    -> next l x
          | otherwise -> t
{-
        next    RNull x                         =   RNull
        next    t@(RNode (BS.empty) _ _) x      = t   
        next    t@(RNode (v:vs) l r)  x
                |v == x                     =   next l x
                |otherwise                  =   t
-}
-- Run the automaton, return 0-based start positions (overlapping)
repMatchPositions :: BS.ByteString -> BS.ByteString -> [Int]
repMatchPositions pat hay
  | BS.null pat = [0 .. BS.length hay]
  | otherwise   = reverse matches
  where
    root = buildRep pat
    m    = BS.length pat

    ok (RNode vs _ _) = BS.null vs
    ok RNull          = False

    step (!n, !t, acc) x =
      let n' = n + 1
          t' = case t of
                 RNull        -> root
                 RNode vs l r ->
                   if BS.null vs then stepFail l x
                   else if BS.head vs == x then r else stepFail l x
          stepFail RNull y = root
          stepFail (RNode vs l r) y =
            if BS.null vs then stepFail l y
            else if BS.head vs == y then r else stepFail l y
      in if ok t' then (n', t', (n' - m) : acc) else (n', t', acc)

    (_, _, matches) = BS.foldl' step (0, root, []) hay

--------------------------------------------------------------------------------
-- Baselines

-- Overlapping matches using breakSubstring (simple)
bsAllMatchesOverlap :: BS.ByteString -> BS.ByteString -> [Int]
bsAllMatchesOverlap needle hay
  | BS.null needle = [0 .. BS.length hay]
  | BS.length needle > BS.length hay = []
  | otherwise = go 0 hay []
  where
    go !off !rest acc =
      case BS.breakSubstring needle rest of
        (pre, suf)
          | BS.null suf -> reverse acc
          | otherwise   ->
              let pos   = off + BS.length pre
                  rest' = BS.drop 1 suf  -- allow overlapping matches
              in go (pos + 1) rest' (pos : acc)

-- Naïve O(n·m) overlapping matcher
naiveAllMatches :: BS.ByteString -> BS.ByteString -> [Int]
naiveAllMatches needle hay
  | BS.null needle = [0 .. BS.length hay]
  | BS.length needle > BS.length hay = []
  | otherwise =
      let n = BS.length needle
          limit = BS.length hay - n
      in [ i
         | i <- [0 .. limit]
         , BS.take n (BS.drop i hay) == needle
         ]

--------------------------------------------------------------------------------
--------------------------------------------------------------------------------
-- Types & combined search across contigs

data Contig = Contig
  { cname :: !BS.ByteString
  , cbs   :: !BS.ByteString
  , cvec  :: !(U.Vector Word8)
  , coff  :: !Int               -- 0-based offset within original contig
  }

data Env = Env
  { contigs   :: ![Contig]
  , needleBS  :: !BS.ByteString
  , needleVec :: !(U.Vector Word8)
  , needleLPS :: !(U.Vector Int)
  }
-----------------------------------------------------------------------------

-- FASTA parsing (strict) for "load all" path

-- Returns [(contigName, sequence)] with sequence cleaned & uppercased.
parseFASTA :: BS.ByteString -> [(BS.ByteString, BS.ByteString)]
parseFASTA raw = go (B8.lines raw) [] Nothing BS.empty
  where
    flush acc mname seqAcc =
      case mname of
        Nothing -> acc
        Just nm -> (nm, seqAcc) : acc

    go [] acc mname seqAcc =
      reverse (flush acc mname (cleanDNA seqAcc))
    go (ln:rest) acc mname seqAcc
      | B8.null ln = go rest acc mname seqAcc
      | B8.head ln == '>' =
          let name   = B8.takeWhile (not . isSpace) (B8.tail ln)
              acc'   = flush acc mname (cleanDNA seqAcc)
          in go rest acc' (Just name) BS.empty
      | otherwise =
          go rest acc mname (seqAcc <> ln)

readFASTA :: FilePath -> IO [(BS.ByteString, BS.ByteString)]
readFASTA fp = do
  lbs0 <- BL.readFile fp
  let isGz = takeExtension fp == ".gz" || BL.take 2 lbs0 == BL.pack [0x1f,0x8b]
      lbs  = if isGz then GZip.decompress lbs0 else lbs0
  let xs  = parseFASTA (BL.toStrict lbs)
  when (null xs) $
    fail "FASTA parser: no sequences found"
  pure xs

--------------------------------------------------------------------------------
-----------------------------------------------------------------------------

-- Synthetic fallback when no files are provided.
syntheticLibrary :: IO [Contig]
syntheticLibrary = do
  let unit = B8.pack "ACGTACGTACGTACGTACGTNNNNACGTACGTACGTACGTACGTACGTACGTAC\n"
      hay  = BS.concat (replicate 400000 unit)
      nm   = B8.pack "chrSynthetic"
  pure [ Contig nm hay (toVecBS hay) 0 ]
-----------------------------------------------------------------------------
-- Streaming slice loader for ROI (fast on hg38)

-- Read only the requested contig and slice (1-based start, fixed len).
-- Works on .fa and .fa.gz; returns a strict ByteString of the slice.
readFastaSlice :: FilePath -> BS.ByteString -> Int -> Int -> IO BS.ByteString
readFastaSlice fp nm start1 len = do
  lbs0 <- BL.readFile fp
  let isGz = takeExtension fp == ".gz" || BL.take 2 lbs0 == BL.pack [0x1f,0x8b]
      lbs  = if isGz then GZip.decompress lbs0 else lbs0  -- still lazy
  let needDrop0 = max 0 (start1 - 1)
  let go :: [BL.ByteString] -> Bool -> Int -> Int -> [BS.ByteString] -> IO BS.ByteString
      go [] _ _ takeN acc = pure (BS.concat (reverse acc))
      go (ln:rest) inTarget dropN takeN acc
        | BL8.null ln = go rest inTarget dropN takeN acc
        | BL8.head ln == '>' =
            let name = BL.toStrict (BL8.takeWhile (not . isSpace) (BL.tail ln))
            in go rest (name == nm) dropN takeN acc
        | not inTarget = go rest inTarget dropN takeN acc
        | otherwise = do
            -- sequence line: normalize, then drop/take relative to ROI
            let strictLine = BL.toStrict ln
                seqLine    = B8.filter (/= '\r') strictLine
                normLine   = B8.map normalizeDNAChar seqLine
                lineLen    = BS.length normLine

                dropHere   = min dropN lineLen
                afterDrop  = if dropN > 0 then BS.drop dropHere normLine else normLine
                dropN'     = dropN - dropHere

                takeHere   = min takeN (BS.length afterDrop)
                chunk      = BS.take takeHere afterDrop
                takeN'     = takeN - takeHere
                acc'       = if takeHere > 0 then chunk : acc else acc
            if takeN' == 0
               then pure (BS.concat (reverse acc'))
               else go rest inTarget dropN' takeN' acc'
  go (BL8.lines lbs) False needDrop0 len []

--------------------------------------------------------------------------------
-----------------------------------------------------------------------------
-- Segment (pattern) argument

-- Accepts:
--   "ACGT..."                          -- literal
--   "@file.fa"                         -- first contig, whole
--   "@file.fa:contig:start+len"        -- 1-based start, fixed length
--   "@file.fa:contig:start-end"        -- 1-based inclusive range
readSegmentArg :: String -> IO BS.ByteString
readSegmentArg s
  | '@':rest <- s = readSegFromFASTA rest
  | otherwise     = pure (cleanDNA (B8.pack s))

data Slice = Slice  -- contig and 1-based coordinates
  { sContig :: !BS.ByteString
  , sStart1 :: !Int
  , sLen    :: !Int
  }

readSegFromFASTA :: String -> IO BS.ByteString
readSegFromFASTA spec = do
  let (fp, more) = break (== ':') spec
  xs <- readFASTA fp
  case more of
    ""       -> pure (snd (head xs))
    ':' : rs ->
      case parseSliceSpec rs of
        Left e -> fail ("segment slice parse error: " ++ e)
        Right (Slice nm start1 len) ->
          case find (\(n,_) -> n == nm) xs of
            Nothing        -> fail ("contig not found in " ++ fp ++ ": " ++ B8.unpack nm)
            Just (_, seqB) ->
              let s0  = max 0 (start1 - 1)
                  seg = BS.take len (BS.drop s0 (cleanDNA seqB))
              in pure seg
-----------------------------------------------------------------------------
-- Vector-KMP across contigs (absolute positions with +coff)
kmpAllContigs :: Env -> [(BS.ByteString, Int)]
kmpAllContigs env =
  concatMap per (contigs env)
  where
    per c =
      let psRel = kmpSearchAll (needleVec env) (needleLPS env) (cvec c)
      in map (\p -> (cname c, p + coff c)) psRel

-- Rep-automaton across contigs
repAllContigs :: Env -> [(BS.ByteString, Int)]
repAllContigs env =
  concatMap per (contigs env)
  where
    per c =
      map (\p -> (cname c, p + coff c)) (repMatchPositions (needleBS env) (cbs c))

-- Baselines across contigs (adjust to absolute coords)
bsAllContigs :: Env -> [(BS.ByteString, Int)]
bsAllContigs env =
  concatMap per (contigs env)
  where
    per c =
      map (\p -> (cname c, p + coff c)) (bsAllMatchesOverlap (needleBS env) (cbs c))

naiveAllContigs :: Env -> [(BS.ByteString, Int)]
naiveAllContigs env =
  concatMap per (contigs env)
  where
    per c =
      map (\p -> (cname c, p + coff c)) (naiveAllMatches (needleBS env) (cbs c))

--------------------------------------------------------------------------------
-----------------------------------------------------------------------------
-- Loaders

-- Load entire FASTA (all contigs)
loadLibrary :: FilePath -> IO [Contig]
loadLibrary fp = do
  xs <- readFASTA fp
  pure [ Contig nm seqBS (toVecBS seqBS) 0 | (nm, seqBS) <- xs ]

-- Load only the ROI slice (fast for huge genomes)
loadLibraryROI :: FilePath -> RegionSpec -> IO [Contig]
loadLibraryROI _ ROIAll = fail "ROIAll is not a concrete region"
loadLibraryROI fp (ROIRange nm s1 l) = do
  putStrLn $ "loadLibraryROI " ++ show fp
  slice <- readFastaSlice fp nm s1 l
  when (BS.null slice) $
    fail ("ROI slice is empty; check contig name and coordinates: " ++ B8.unpack nm)
  pure [ Contig nm slice (toVecBS slice) (max 0 (s1 - 1)) ]

-----------------------------------------------------------------------------
-- Build the Env
setupEnv :: Maybe FilePath -> Maybe String -> Maybe RegionSpec -> IO Env
setupEnv mLib mSeg mROI = do
  conts0 <-
    case (mLib, mROI) of
      (Nothing , _)                          -> syntheticLibrary
      (Just fp , Just r@(ROIRange _ _ _))    -> loadLibraryROI fp r
      (Just fp , _                        )  -> loadLibrary fp
  let conts = conts0
  seg <- maybe (pure (B8.pack "ACGTACGTAC")) readSegmentArg mSeg
  let seg' = cleanDNA seg
      pv   = toVecBS seg'
      lps  = buildLPS pv
  when (BS.null seg') $ fail "Segment is empty after cleaning."
  pure Env { contigs   = conts
           , needleBS  = seg'
           , needleVec = pv
           , needleLPS = lps
           }

--------------------------------------------------------------------------------
--------------------------------------------------------------------------------
-- "find" mode: print all matches (0-based) as <contig>\t<pos>

runFind :: [String] -> IO ()
runFind args = do
  env <- case args of
           [lib, seg] -> setupEnv (Just lib) (Just seg) Nothing
           [seg]      -> setupEnv Nothing (Just seg) Nothing
           []         -> setupEnv Nothing Nothing Nothing
           _          -> fail "Usage: find [<library.fasta>] <segment|@segment.fasta>"
  let matches = kmpAllContigs env
  mapM_ (\(nm, p) -> B8.putStrLn (nm <> B8.pack "\t" <> B8.pack (show p))) matches
  B8.putStrLn (B8.pack ("# total matches: " ++ show (length matches)))

-- ROI-aware "find"
runFindWithROI :: Maybe RegionSpec -> [String] -> IO ()
runFindWithROI mROI args = do
  env <- case args of
           [lib, seg] -> setupEnv (Just lib) (Just seg) mROI
           [seg]      -> setupEnv Nothing (Just seg) mROI
           []         -> setupEnv Nothing Nothing mROI
           _          -> fail "Usage: find [--roi contig:start+len] [<library.fasta>] <segment|@segment.fasta>"
--  let matches = kmpAllContigs env

  let matches = repAllContigs env
  mapM_ (\(nm, pAbs) -> B8.putStrLn (nm <> B8.pack "\t" <> B8.pack (show pAbs))) matches
  B8.putStrLn (B8.pack ("# total matches: " ++ show (length matches)))

-------------------------------------------------------------------------------
parseSliceSpec :: String -> Either String Slice
parseSliceSpec s =
  case break (== ':') s of
    (contigStr, ':' : rest) ->
      let contig = B8.pack contigStr
      in case break (`elem` "+-") rest of
           (startStr, op:lenEndStr)
             | all isDigit startStr ->
               let start1 = read startStr
               in case op of
                    '+' | all isDigit lenEndStr ->
                          Right (Slice contig start1 (read lenEndStr))
                    '-' | all isDigit lenEndStr ->
                          let end1 = read lenEndStr
                          in Right (Slice contig start1 (max 0 (end1 - start1 + 1)))
                    _ -> Left "need '+' length or '-' end after start"
           _ -> Left "expected start+len or start-end after contig:"
    _ -> Left "expected contig:start+len or contig:start-end"
--------------------------------------------------------------------------------
-- ROI spec

data RegionSpec
  = ROIAll
  | ROIRange { roiName :: !BS.ByteString, roiStart1 :: !Int, roiLen :: !Int } deriving(Show)

parseROIRange :: String -> Either String RegionSpec
parseROIRange s =
  case parseSliceSpec s of
    Left e -> Left e
    Right (Slice nm s1 len) -> Right (ROIRange nm s1 len)

-- Accept --roi=chr:start+len OR --roi chr:start+len
parseArgsROI :: [String] -> Either String (Maybe RegionSpec, [String])
parseArgsROI = go Nothing []
  where
    go m acc [] = Right (m, reverse acc)
    go m acc ("--roi":spec:xs) =
      case parseROIRange spec of
        Left e  -> Left ("--roi parse error: " ++ e)
        Right r -> go (Just r) acc xs
    go m acc (o:xs)
      | "--roi=" `isPrefixOf` o =
          case parseROIRange (drop (length "--roi=") o) of
            Left e  -> Left ("--roi parse error: " ++ e)
            Right r -> go (Just r) acc xs
      | otherwise = go m (o:acc) xs

--------------------------------------------------------------------------------
splitAtDoubleDash :: [String] -> ([String], [String])
splitAtDoubleDash = go [] where
  go acc []           = (reverse acc, [])
  go acc ("--":rest)  = (reverse acc, rest)  -- second `--` sentinel
  go acc (x:xs)       = go (x:acc) xs
---------------------------------------------------------------------------------

main :: IO ()
main = do
--    putStrLn $ reverse "Hello, Haskell!"
--    print $ match "bbc" "bbbbbc"
    
    argv <- getArgs
--    print $ argv
    let (ours,crit) = splitAtDoubleDash argv
    
    case parseArgsROI ours of
        Left e -> fail e
        Right (mROI,positional) ->
            case positional of
                ("find":rest) -> do
                                    before <- getCurrentTime
                                    runFindWithROI mROI rest
                                    after  <- getCurrentTime
                                    
                                    let mark1 = realToFrac $ utctDayTime before :: Double
                                        mark2 = realToFrac $ utctDayTime after  :: Double
                                    print ("spent = " ++ show (mark2 - mark1))

                _             -> fail "Usage"
