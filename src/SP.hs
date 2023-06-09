{-# LANGUAGE DataKinds #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE RecordWildCards #-}

module SP where

import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import Data.Sequence (Seq (..), (<|))
import Unsafe.Coerce (unsafeCoerce)
import Data.Maybe (fromJust)
import qualified Data.Sequence as Seq
import Debug.Trace (trace)
import GHC.Exts (IsList(toList))

{- | SP
Get (\x -> SP i o)
Put o (SP i o)
-}
data SP i o
  = Get (i -> SP i o)
  | Put o (SP i o)

data SPWrapper i o = SPWrapper
  { ioIndex :: (Int, Int)
  , sp :: SP i o
  }



data SomeVal = forall a. SomeVal a
data SomeSP = forall i o. SomeSP (SPWrapper i o)


--------------------------------------------------------------------
data ChanState = ChanState {
  chan :: Seq SomeVal
, waitingList :: Seq SomeSP
}

readChan :: SomeSP -> ChanState -> (ChanState, Maybe SomeVal)
readChan ssp cs@ChanState{..} = case chan of
  Empty -> (cs{waitingList= waitingList :|> ssp}, Nothing)
  (v :<| vs) -> (cs{chan = vs}, Just v)

writeChan :: SomeVal -> ChanState -> (ChanState, Maybe SomeSP) 
writeChan sv cs@ChanState{..} = case waitingList of
  Empty -> (cs{chan= chan :|> sv}, Nothing)
  (sp :<| sps ) -> ( cs{ chan= chan :|> sv
                       , waitingList = sps}
                   , Just sp)
--------------------------------------------------------------------
type RunningList =  Seq SomeSP

data EvalState = EvalState {
  chans :: IntMap ChanState
, runningList :: RunningList
}

run :: EvalState -> EvalState
run es@EvalState{..} = case runningList of
  Empty -> es
  (ssp@(SomeSP (SPWrapper io@(i, o) sp)) :<| sps) -> case sp of
    Get f -> let cs = fromJust $ IntMap.lookup i chans
                 (cs', mv) = readChan ssp cs
                 chans' = IntMap.insert i cs' chans
        in case  mv of
            Just (SomeVal val) ->
                 let ssp' = SomeSP $ SPWrapper io $ f (unsafeCoerce val)
                 in run es{chans = chans'
                      ,runningList = sps :|> ssp'}
            Nothing -> run $  es{chans = chans'
                         ,runningList = sps}
    Put v sp' -> let cs = fromJust $ IntMap.lookup o chans
                     (cs', msp) = writeChan (SomeVal v) cs
                     chans' = IntMap.insert o cs' chans
       in case  msp of
        Nothing -> run es{chans = chans' 
                         ,runningList = sps :|> (SomeSP $ SPWrapper io sp')}
        Just sssp -> run es{chans = chans' 
                           ,runningList = sps :|> sssp :|> (SomeSP $ SPWrapper io sp')}

es1 = EvalState {
  chans = IntMap.fromList [ (0, ChanState (Seq.fromList $ map SomeVal [0 :: Int, 1 ,2]) Seq.empty)
                          , (1, ChanState (Seq.fromList $ map SomeVal [1000 :: Int .. 1003]) Seq.empty)
                          , (2, ChanState Seq.empty Seq.empty)
                          , (3, ChanState Seq.empty Seq.empty)
                          ]
, runningList = Seq.fromList [ SomeSP $ SPWrapper (0,1) fsp
                             , SomeSP $ SPWrapper (1,2) fsp
                             , SomeSP $ SPWrapper (2,3) (fsum 0)
                             ]
}

fsp :: SP Int Int
fsp = Get $ \x -> Put (x+1) fsp

fsum :: Int -> SP Int Int
fsum i = Get $ \x -> Put (i+x) (fsum (i+x))

-- >>> rs1
-- [fromList [(0,[0,1,2]),(1,[1000]),(2,[])],fromList [(0,[]),(1,[]),(2,[1001,2,3,4])]]
rs1 :: [IntMap [Int]]
rs1 = let es1' =  run es1
  in [hf es1, hf es1']

hf = IntMap.map (chan2v . chan) . chans


chan2v :: Seq SomeVal -> [v]
chan2v s = toList $ fmap (\(SomeVal v) -> unsafeCoerce v) s
