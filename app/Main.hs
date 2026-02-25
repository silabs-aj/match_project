{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE PackageImports #-}

import Debug.Trace

-- module Main where  -- (optional)

import Data.Time.Clock
import System.Environment (getArgs)
import System.FilePath (takeExtension)

-- import Criterion.Main -- (unused; remove if not needed)
import Control.Monad (when)
-- *** MODIFIED: removed Codec.Compression.GZip / lazy ByteString file reading
import qualified Data.ByteString as BS
import qualified Data.ByteString.Char8 as B8
import qualified Data.ByteString.Lazy as BL
import qualified Data.ByteString.Lazy.Char8 as BL8

import Data.Char (isDigit, isSpace, toUpper)
import Data.List (find, partition, isPrefixOf)

import qualified Data.Vector.Unboxed as U
import qualified Data.Vector.Unboxed.Mutable as M
import Data.Word (Word8)

-- *** MODIFIED: conduit imports
import Control.Monad.Catch (MonadThrow)
import Control.Monad.IO.Class (MonadIO, liftIO)
import Control.Monad.Trans.Resource (ResourceT, runResourceT, MonadResource)
import qualified Data.Conduit as C              -- C.ConduitT, C.await, C.yield, C.bracketP, C.runConduit
import qualified Data.Conduit.Binary as CB      -- CB.sourceHandle, CB.lines
import qualified Data.Conduit.Combinators as CC -- CC.sinkList, CC.head
import qualified Data.Conduit.Zlib as CZ        -- CZ.ungzip
-- *** MODIFIED: file handle + builder
import System.IO (IOMode(ReadMode), openBinaryFile, hClose, hSeek, SeekMode(AbsoluteSeek))
import qualified Data.ByteString.Builder as BB

--data Rep a = Null | Node [a] (Rep a) (Rep a) deriving (Show)

{-  (omitted historical notes)
match   ws  =   map fst . filter (ok . snd) . scanl step (0,root)
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

-- *** MODIFIED: strip CR for CRLF files
stripCR :: BS.ByteString -> BS.ByteString
stripCR = B8.filter (/= '\r')

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

    next :: Rep -> Word8 -> Rep
    next RNull _ = RNull
    next t@(RNode vs l _) x =
      case BS.uncons vs of
        Nothing       -> t
        Just (v, _)
          | v == x    -> next l x
          | otherwise -> t

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

-- FASTA parsing (strict) for "load all" path (kept for reference; unused in streaming path)
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

-- *** MODIFIED: streaming file source with optional gzip
sourcePossiblyGzip :: (MonadResource m, MonadIO m,MonadThrow m, M.PrimMonad m)
                   => FilePath -> C.ConduitT () BS.ByteString m ()
sourcePossiblyGzip fp =
  C.bracketP (openBinaryFile fp ReadMode) hClose $ \h -> do
    magic <- liftIO (BS.hGet h 2)
    liftIO (hSeek h AbsoluteSeek 0)
    let isGz = takeExtension fp == ".gz" || magic == BS.pack [0x1f, 0x8b]
        src  = CB.sourceHandle h
    if isGz then src C..| CZ.ungzip else src

-- *** MODIFIED: streaming FASTA record conduit
fastaRecordsC
  :: Monad m
  => C.ConduitT BS.ByteString (BS.ByteString, BS.ByteString) m ()
fastaRecordsC = go Nothing mempty
  where
    finalize = BL.toStrict . BB.toLazyByteString
    push nm acc = C.yield (nm, finalize acc)

    go mName acc = do
      mLine <- C.await
      case mLine of
        Nothing ->
          case mName of
            Nothing -> pure ()
            Just nm -> push nm acc
        Just ln0 -> do
          let ln = stripCR ln0
          if BS.null ln
            then go mName acc
            else if B8.head ln == '>'
              then do
                -- header line
                let nm = B8.takeWhile (not . isSpace) (BS.tail ln)
                case mName of
                  Nothing  -> go (Just nm) mempty
                  Just nm' -> push nm' acc >> go (Just nm) mempty
              else do
                -- sequence line (clean + append)
                let cleaned = cleanDNA ln
                go mName (acc <> BB.byteString cleaned)

-- *** MODIFIED: streaming readFASTA
readFASTA :: FilePath -> IO [(BS.ByteString, BS.ByteString)]
readFASTA fp = do
  xs <- runResourceT $
          C.runConduit $
            sourcePossiblyGzip fp
        C..| CB.lines
        C..| fastaRecordsC
        C..| CC.sinkList
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
-- *** MODIFIED: Streaming slice loader for ROI (fast on hg38)
-- Read only the requested contig and slice (1-based start, fixed len).
-- Works on .fa and .fa.gz; returns a strict ByteString of the slice.
readFastaSlice :: FilePath -> BS.ByteString -> Int -> Int -> IO BS.ByteString
readFastaSlice fp nm start1 len =
  runResourceT $
    C.runConduit $
         sourcePossiblyGzip fp
    C..| CB.lines
    C..| sinkSlice nm (max 0 (start1 - 1)) len
  where
    sinkSlice
      :: Monad m
      => BS.ByteString        -- target contig name
      -> Int                  -- dropN: how many bases to drop at start
      -> Int                  -- takeN: how many bases to take
      -> C.ConduitT BS.ByteString o m BS.ByteString
    sinkSlice target dropN0 takeN0 = go False dropN0 takeN0 mempty
      where
        finalize = BL.toStrict . BB.toLazyByteString
        go inTarget dropN takeN acc
          | takeN <= 0 = pure (finalize acc)
          | otherwise = do
              mLine0 <- C.await
              case mLine0 of
                Nothing -> pure (finalize acc)
                Just ln0 -> do
                  let ln = stripCR ln0
                  if BS.null ln
                    then go inTarget dropN takeN acc
                    else if B8.head ln == '>'
                      then
                        let name = B8.takeWhile (not . isSpace) (BS.tail ln)
                        in go (name == target) dropN takeN acc
                      else if not inTarget
                        then go inTarget dropN takeN acc
                        else do
                          let normLine    = B8.map normalizeDNAChar ln
                              lineLen     = BS.length normLine
                              dropHere    = min dropN lineLen
                              afterDrop   = if dropN > 0 then BS.drop dropHere normLine else normLine
                              dropN'      = dropN - dropHere
                              takeHere    = min takeN (BS.length afterDrop)
                              takeN'      = takeN - takeHere
                              chunk       = BS.take takeHere afterDrop
                              acc'        = if takeHere > 0
                                              then acc <> BB.byteString chunk
                                              else acc
                          if takeN' <= 0
                            then pure (finalize acc')
                            else go inTarget dropN' takeN' acc'

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

-- *** MODIFIED: stream only what’s needed
readSegFromFASTA :: String -> IO BS.ByteString
readSegFromFASTA spec = do
  let (fp, more) = break (== ':') spec
  case more of
    "" -> do
      -- Only the first record (streaming)
      mh <- runResourceT $
              C.runConduit $
                   sourcePossiblyGzip fp
              C..| CB.lines
              C..| fastaRecordsC
              C..| CC.head
      case mh of
        Nothing        -> fail ("no sequences found in " ++ fp)
        Just (_, seqB) -> pure seqB
    ':' : rs ->
      case parseSliceSpec rs of
        Left e -> fail ("segment slice parse error: " ++ e)
        Right (Slice nm start1 l) -> do
          slice <- readFastaSlice fp nm start1 l
          -- 'slice' already normalized to A/C/G/T/N; 'cleanDNA' is safe but optional
          pure (cleanDNA slice)
-----------------------------------------------------------------------------
-- Streaming FASTA validator (useful for very large hg38.fa.gz files)

data FastaValidation = FastaValidation
  { fvContigs            :: !Int
  , fvBases              :: !Int
  , fvNonACGTN           :: !Int
  , fvSeqLinesNoHeader   :: !Int
  } deriving (Show)

validateFastaLikeHg38 :: FilePath -> IO FastaValidation
validateFastaLikeHg38 fp =
  runResourceT $
    C.runConduit $
         sourcePossiblyGzip fp
    C..| CB.lines
    C..| sinkValidate
  where
    sinkValidate :: Monad m => C.ConduitT BS.ByteString o m FastaValidation
    sinkValidate = go False 0 0 0 0

    go inHeaderSeen !contigs !bases !nonACGTN !seqLinesNoHeader = do
      mLine0 <- C.await
      case mLine0 of
        Nothing ->
          pure (FastaValidation contigs bases nonACGTN seqLinesNoHeader)
        Just ln0 -> do
          let ln = stripCR ln0
          if BS.null ln
            then go inHeaderSeen contigs bases nonACGTN seqLinesNoHeader
            else if B8.head ln == '>'
              then
                let name = B8.takeWhile (not . isSpace) (BS.tail ln)
                in if BS.null name
                     then go True contigs bases nonACGTN (seqLinesNoHeader + 1)
                     else go True (contigs + 1) bases nonACGTN seqLinesNoHeader
              else
                let lineLen = BS.length ln
                    badHere = BS.length (B8.filter (not . isDNAChar) ln)
                    seqLinesNoHeader' = if inHeaderSeen then seqLinesNoHeader else seqLinesNoHeader + 1
                in go inHeaderSeen contigs (bases + lineLen) (nonACGTN + badHere) seqLinesNoHeader'

    isDNAChar c =
      case toUpper c of
        'A' -> True
        'C' -> True
        'G' -> True
        'T' -> True
        'N' -> True
        _   -> False

runValidateHg38 :: [String] -> IO ()
runValidateHg38 args = do
  let fp = case args of
             []      -> "hg38.fa.gz"
             [one]   -> one
             _       -> error "Usage: validate-hg38 [<hg38.fa.gz>]"
  v <- validateFastaLikeHg38 fp
  putStrLn ("validate-hg38 file: " ++ fp)
  putStrLn ("contigs: " ++ show (fvContigs v))
  putStrLn ("bases: " ++ show (fvBases v))
  putStrLn ("non-ACGTN bases: " ++ show (fvNonACGTN v))
  putStrLn ("sequence lines without header: " ++ show (fvSeqLinesNoHeader v))
  when (fvContigs v <= 0) $ fail "validation failed: no FASTA headers found"
  when (fvSeqLinesNoHeader v > 0) $ fail "validation failed: sequence lines encountered before a valid header"
  when (fvNonACGTN v > 0) $
    putStrLn "warning: non-ACGTN symbols present; readFastaSlice will normalize these to 'N'"

-------------------------------------------------------------------------
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
  putStrLn $ "nm : " ++ show nm ++ " s1 = " ++ show s1 
  pure [ Contig nm slice (toVecBS slice) (max 0 (s1 - 1)) ]

-----------------------------------------------------------------------------
-- Build the Env
setupEnv :: Maybe FilePath -> Maybe String -> Maybe RegionSpec -> IO Env
setupEnv mLib mSeg mROI = do
  putStrLn $ "mLib File Name: " ++ show mLib ++ " mSeg =" ++ show mSeg ++ " mROI = " ++ show mROI
  conts0 <-
    case (mLib, mROI) of
      (Nothing , _)                          -> syntheticLibrary
      (Just fp , Just r@(ROIRange _ _ _))    -> loadLibraryROI fp r
      (Just fp , _)                          -> loadLibrary fp
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
           [lib, seg] -> trace ("seg : " ++ show seg) $ setupEnv (Just lib) (Just seg) mROI
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
    go m acc [] = trace (" m " ++ show m ++ " acc = " ++ show (reverse acc)) $ Right (m, reverse acc)
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
    argv <- getArgs
    let (ours,crit) = splitAtDoubleDash argv
    putStrLn("ours = " ++ show ours)
    putStrLn("crit = " ++ show crit)
    case parseArgsROI ours of
      Left e -> fail e
      Right (mROI,positional) ->
        case positional of
          ("validate-hg38":rest) -> runValidateHg38 rest
          ("find":rest) -> do
            before <- getCurrentTime
            runFindWithROI mROI rest
            after  <- getCurrentTime
            let mark1 = realToFrac $ utctDayTime before :: Double
                mark2 = realToFrac $ utctDayTime after  :: Double
            print ("spent = " ++ show (mark2 - mark1))
          _ -> fail "Usage"

