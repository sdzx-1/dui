{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}

module SP.Gen where

import Control.Algebra (Has, (:+:))
import Control.Carrier.Fresh.Strict (fresh, runFresh)
import Control.Carrier.Lift (runM)
import Control.Carrier.State.Strict (State, runState)
import Control.Effect.Fresh (Fresh)
import Control.Effect.Optics (assign, modifying, preuse)
import Control.Monad (forM_, replicateM)
import qualified Data.Sequence as Seq
import Optics (At (at), Ixed (ix), (%))
import SP.Type
import SP.Util

data GenResult = GenResult
  { -- | all (:>>+) First Branch ChanState index collects
    allBFCI :: [ChanIndex],
    -- | LSP output ChanState index
    lspOI :: ChanIndex,
    -- | all RTSP index list
    allRTSPI :: [Int],
    -- | all ChanState index list
    allCSI :: [ChanIndex],
    -- | all Dyn Special Num list
    allDynSN :: [DynSpecialNum]
  }

genES' ::
  ( Has (State EvalState :+: Fresh) sig m,
    MonadFail m
  ) =>
  ChanIndex ->
  LSP xs i o ->
  m GenResult
genES' i (E sp) = do
  i' <- newCSIndex
  index <- addRTSP $ SomeSP $ SPWrapper (i, i') sp
  pure $ GenResult [] i' [index] [i'] []
genES' i (lsp :>>> lsps) = do
  GenResult ots1 i' i1s c1s d1s <- genES' i lsp
  GenResult ots2 i'' i2s c2s d2s <- genES' i' lsps
  pure $ GenResult (ots1 ++ ots2) i'' (i1s ++ i2s) (c1s ++ c2s) (d1s ++ d2s)
genES' i ((:+++) lsp rsp) = do
  lo <- newCSIndex
  ro <- newCSIndex
  ie <- addRTSP $ EitherUp i (lo, ro)
  GenResult lots lo' i1s c1s d1s <- genES' lo lsp
  GenResult rots ro' i2s c2s d2s <- genES' ro rsp
  ko <- newCSIndex
  ies <-
    addRTSPList
      [ EitherDownLeft lo' ko,
        EitherDownRight ro' ko
      ]
  pure $
    GenResult
      (lots ++ rots)
      ko
      (i1s ++ i2s ++ [ie] ++ ies)
      (c1s ++ c2s ++ [lo, ro, ko])
      (d1s ++ d2s)
genES' i (LoopEither lsp) = do
  i1 <- newCSIndex
  il <- addRTSP $ EitherDownLeft i i1
  GenResult ots o1 is c1s d1s <- genES' i1 lsp
  leftO <- newCSIndex
  ill <- addRTSP $ LoopEitherDown o1 (leftO, i1)
  pure $ GenResult ots leftO (is ++ [il, ill]) (c1s ++ [i1, leftO]) d1s
genES' i (lsp :*** rsp) = do
  fsto <- newCSIndex
  sndo <- newCSIndex
  it <- addRTSP $ TupleUp i (fsto, sndo)
  GenResult fots fsto' i1s c1s d1s <- genES' fsto lsp
  GenResult sots sndo' i2s c2s d2s <- genES' sndo rsp
  ko <- newCSIndex
  its <-
    addRTSPList
      [ TupleDownFst fsto' sndo' ko,
        TupleDownSnd sndo' fsto' ko
      ]
  pure $
    GenResult
      (fots ++ sots)
      ko
      (i1s ++ i2s ++ [it] ++ its)
      (c1s ++ c2s ++ [fsto, sndo, ko])
      (d1s ++ d2s)
genES' i (lsp :>>+ rsp) = do
  fsto <- newCSIndex
  sndo <- newCSIndex
  ib <- addRTSP $ Both i (fsto, sndo)
  GenResult fots fsto' i1s c1s d1s <- genES' fsto lsp
  GenResult sots sndo' i2s c2s d2s <- genES' sndo rsp
  pure $
    GenResult
      (fots ++ [fsto'] ++ sots)
      sndo'
      (i1s ++ i2s ++ [ib])
      (c1s ++ c2s ++ [fsto, sndo])
      (d1s ++ d2s)
genES' i (Dyn :: LSP xs i o) = do
  o <- newCSIndex
  os <- replicateM (hListLength @xs) newCSIndex
  sn <- DynSpecialNum <$> fresh
  index <-
    addRTSP $
      DynSP
        ( DynSPState
            { upstreamChan = i,
              downstreamChan = o,
              dynSpecialNum = sn,
              debugOutputs = os
            }
        )
        (Action dynSP)
  pure $ GenResult os o [index] (o : os) [sn]
genES' i DebugRt = do
  o <- newCSIndex
  output <- newCSIndex
  index <- addRTSP $ DebugRtSP output i o
  pure $ GenResult [output] o [index] (o : [output]) []

genES :: MonadFail m => [i] -> LSP xs i o -> m (EvalState, (Int, GenResult))
genES ls lsp =
  runM $
    runState @EvalState (initEvalState ls) $
      runFresh 1 (genES' (intToChanIndex 0) lsp)

-- genESArrest :: MonadFail m => LSP xs i o -> m ()
-- genESArrest lsp = do
--   (es, (_, GenResult _ _ ls css _)) <- genES [] lsp
--   let spIndexs = map extraIndex $ toList $ es ^. #runningList
--       chans = map fst $ IntMap.toList $ es ^. #chans
--   if (sort spIndexs == sort ls) && (sort chans == sort (0 : css))
--     then pure ()
--     else
--       error $
--         "generate lsp to EvalState error: "
--           ++ show (spIndexs, ls)
--           ++ show (chans, 0 : css)

-------------------------------------------------------

dynSP ::
  forall a b sig m.
  ( MonadFail m,
    Has (State EvalState :+: State DynMap :+: Fresh) sig m
  ) =>
  DynSPState ->
  Either (LSP '[] a b) a ->
  m ()
dynSP dys@(DynSPState _ _downc dsn _) upVal = do
  mst <- preuse @DynMap (ix dsn)
  case upVal of
    Right a -> case mst of
      Nothing -> pure ()
      Just (LspGenState _ si _ _ _) -> writeVal (SomeVal a) si
    Left lsp -> do
      case mst of
        Just _ -> do
          -- rec remove exit dyn lsp
          -- need wait all chanstate empty??
          recRemoveDynSP dsn
          -- gen lsp
          dynGenLSP dys lsp
        Nothing -> do
          -- gen lsp
          dynGenLSP dys lsp

recRemoveDynSP ::
  ( MonadFail m,
    Has (State EvalState :+: State DynMap) sig m
  ) =>
  DynSpecialNum ->
  m ()
recRemoveDynSP dsn = do
  mst <- preuse @DynMap (ix dsn)
  case mst of
    Nothing -> pure ()
    Just (LspGenState _ _ artspis acis aadsns) -> do
      -- running list remove
      modifying @_ @EvalState
        #runningList
        (Seq.filter (\(RTSPWrapper i _) -> i `notElem` artspis))
      -- ChanState Map remvoe
      forM_ acis $ \i ->
        assign @EvalState (#chans % at (chanIndexToInt i)) Nothing
      -- rec remvoe Dyn
      assign @DynMap (at dsn) Nothing
      mapM_ recRemoveDynSP aadsns

dynGenLSP ::
  forall a b sig m.
  ( MonadFail m,
    Has (State EvalState :+: State DynMap :+: Fresh) sig m
  ) =>
  DynSPState ->
  LSP '[] a b ->
  m ()
dynGenLSP (DynSPState _ dci dsn dOuputs) lsp = do
  ici <- newCSIndex
  GenResult dbgots lspOI allRTSPI allCSI dspn <- genES' ici lsp
  idx <- addRTSP $ DirectReadWrite lspOI dci
  idxs <- addRTSPList [DirectReadWrite i o | i <- dbgots, o <- dOuputs]
  assign @DynMap (at dsn) $
    Just
      LspGenState
        { lspSource = SomeLSP lsp,
          startChanIndex = ici,
          allRTSPIndexs = allRTSPI ++ [idx] ++ idxs,
          allChanIndexs = allCSI ++ [ici],
          allDynSpecialNum = dspn
        }