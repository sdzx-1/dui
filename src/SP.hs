{-# LANGUAGE DataKinds #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TypeOperators #-}

module SP where

import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import Data.Maybe (fromJust)
import Data.Sequence (Seq (..))
import qualified Data.Sequence as Seq
import GHC.Exts (IsList (toList))
import Unsafe.Coerce (unsafeCoerce)

-- | SP
-- Get (\x -> SP i o)
-- Put o (SP i o)
data SP i o
  = Get (i -> SP i o)
  | Put o (SP i o)

data SPWrapper i o = SPWrapper
  { ioIndex :: (Int, Int),
    sp :: SP i o
  }

data SomeVal = forall a. SomeVal a

data SomeSP
  = forall i o. SomeSP (SPWrapper i o)
  | EitherUp Int (Int, Int)
  | EitherDown (Int, Int) Int

--------------------------------------------------------------------
data ChanState = ChanState
  { chan :: Seq SomeVal,
    waitingList :: Seq SomeSP
  }

initChanState :: ChanState
initChanState =
  ChanState
    { chan = Seq.empty,
      waitingList = Seq.empty
    }

readChan :: SomeSP -> ChanState -> (ChanState, Maybe SomeVal)
readChan ssp cs@ChanState {..} = case chan of
  Empty -> (cs {waitingList = waitingList :|> ssp}, Nothing)
  (v :<| vs) -> (cs {chan = vs}, Just v)

writeChan :: SomeVal -> ChanState -> (ChanState, Maybe SomeSP)
writeChan sv cs@ChanState {..} = case waitingList of
  Empty -> (cs {chan = chan :|> sv}, Nothing)
  (sp :<| sps) ->
    ( cs
        { chan = chan :|> sv,
          waitingList = sps
        },
      Just sp
    )

--------------------------------------------------------------------
type RunningList = Seq SomeSP

data EvalState = EvalState
  { chans :: IntMap ChanState,
    runningList :: RunningList
  }

run :: EvalState -> EvalState
run es@EvalState {..} = case runningList of
  Empty -> es
  sfun :<| sps -> case sfun of
    eup@(EitherUp i (o1, o2)) ->
      let ics = fromJust $ IntMap.lookup i chans
          o1cs = fromJust $ IntMap.lookup o1 chans
          o2cs = fromJust $ IntMap.lookup o2 chans
          -------------------
          (ics', mv) = readChan eup ics
          bbbb = case mv of
            Nothing -> undefined
            Just (SomeVal a) -> case unsafeCoerce a of
              Left lval -> undefined
              Right rval -> undefined
       in undefined
    EitherDown (o1, o2) k -> undefined
    ssp@(SomeSP (SPWrapper io@(i, o) sp)) -> case sp of
      Get f ->
        let cs = fromJust $ IntMap.lookup i chans
            (cs', mv) = readChan ssp cs
            sps' = case mv of
              Just (SomeVal val) ->
                let ssp' = SomeSP $ SPWrapper io $ f (unsafeCoerce val)
                 in sps :|> ssp'
              Nothing -> sps
            es' = es {chans = IntMap.insert i cs' chans, runningList = sps'}
         in run es'
      Put v sp' ->
        let cs = fromJust $ IntMap.lookup o chans
            (cs', msp) = writeChan (SomeVal v) cs
            sps' = case msp of
              Nothing ->
                sps :|> SomeSP (SPWrapper io sp')
              Just sssp ->
                sps :|> sssp :|> SomeSP (SPWrapper io sp')
            es' = es {chans = IntMap.insert o cs' chans, runningList = sps'}
         in run es'

--------------------------------------------------------------------

es1 =
  EvalState
    { chans =
        IntMap.fromList
          [ (0, ChanState (Seq.fromList $ map SomeVal [0 :: Int, 1, 2]) Seq.empty),
            (1, ChanState (Seq.fromList $ map SomeVal [1000 :: Int]) Seq.empty),
            (2, ChanState Seq.empty Seq.empty),
            (3, ChanState Seq.empty Seq.empty)
          ],
      runningList =
        Seq.fromList
          [ SomeSP $ SPWrapper (0, 1) fsp,
            SomeSP $ SPWrapper (1, 2) fsp,
            SomeSP $ SPWrapper (2, 3) (fsum 0)
          ]
    }

fsp :: SP Int Int
fsp = Get $ \x -> Put (x + 1) fsp

fsum :: Int -> SP Int Int
fsum i = Get $ \x -> Put (i + x) (fsum (i + x))

filterSP :: (a -> Bool) -> SP a a
filterSP p = Get $ \x ->
  if p x
    then Put x (filterSP p)
    else filterSP p

arrSP :: (a -> b) -> SP a b
arrSP f = Get $ \x -> Put (f x) (arrSP f)

arrSPState :: s -> (s -> a -> (b, s)) -> SP a b
arrSPState s f = Get $ \a ->
  let (b, s') = f s a
   in Put b (arrSPState s' f)

-- >>> rs1
-- [fromList [(0,[0,1,2]),(1,[1000]),(2,[]),(3,[])],fromList [(0,[]),(1,[]),(2,[]),(3,[1001,1003,1006,1010])]]
rs1 :: [IntMap [Int]]
rs1 =
  let es1' = run es1
   in [hf es1, hf es1']

--------------------------------------------------------------------
hf = IntMap.map (chan2v . chan) . chans

chan2v :: Seq SomeVal -> [v]
chan2v s = toList $ fmap (\(SomeVal v) -> unsafeCoerce v) s
