{-# LANGUAGE GADTs #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TypeOperators #-}

module SP1 where

import qualified Data.IntMap as IntMap
import Data.Sequence
import qualified Data.Sequence as Seq
import SP

infixr 4 :>>>

data LSP i o where
  E :: SP i o -> LSP i o
  (:>>>) :: LSP i o -> LSP o p -> LSP i p

-----------------------
f1 :: LSP Int Int
f1 =
  arrLSP (+ 0)
    :>>> arrLSPState 0 (\s a -> (s + a, s + a))
    :>>> arrLSPState 0 (\s a -> (s + a, s))

arrLSP :: (a -> b) -> LSP a b
arrLSP f = E (arrSP f)

arrLSPState :: s -> (s -> a -> (b, s)) -> LSP a b
arrLSPState s f = E (arrSPState s f)

ge1 = snd $ genES [1, 1, 1, 1] f1

-- >>> re1
-- fromList [(0,[]),(1,[]),(2,[]),(3,[1,2,3,4])]
re1 :: IntMap.IntMap [Int]
re1 = hf $ SP.run ge1

-----------------------

genES' :: Int -> LSP i o -> EvalState -> (Int, EvalState)
genES' i (E sp) es@EvalState {..} =
  let i' = i + 1
      ssp = SomeSP $ SPWrapper (i, i') sp
      es' =
        es
          { chans = IntMap.insert i' initChanState chans,
            runningList = runningList :|> ssp
          }
   in (i', es')
genES' i (lsp :>>> lsps) es =
  let (i', es') = genES' i lsp es
   in genES' i' lsps es'

genES :: [i] -> LSP i o -> (Int, EvalState)
genES ls lsp =
  genES'
    0
    lsp
    EvalState
      { chans =
          IntMap.fromList
            [ ( 0,
                ChanState
                  { chan = Seq.fromList (map SomeVal ls),
                    waitingList = Seq.empty
                  }
              )
            ],
        runningList = Seq.empty
      }
