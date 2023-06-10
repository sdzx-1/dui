{-# LANGUAGE GADTs #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TypeOperators #-}

module SP.SP1 where

import qualified Data.IntMap as IntMap
import Data.Sequence
import qualified Data.Sequence as Seq
import SP.Eval
import SP.Type
import SP.Util


-----------------------
f1 :: LSP Int Int
f1 =
  arrLSP (+ 0)
    :>>> arrLSPState 0 (\s a -> (s + a, s + a))
    :>>> filterLSP even
    -- :>>> arrLSPState 0 (\s a -> (s + a, s))

filterLSP :: (a -> Bool) -> LSP a a
filterLSP p = E (filterSP p)

arrLSP :: (a -> b) -> LSP a b
arrLSP f = E (arrSP f)

arrLSPState :: s -> (s -> a -> (b, s)) -> LSP a b
arrLSPState s f = E (arrSPState s f)

ge1 = snd $ genES [1 .. 10] f1

-- >>> re1
-- fromList [(0,[]),(1,[]),(2,[]),(3,[6,10,28,36])]
re1 :: IO (IntMap.IntMap [Int])
re1 = hf <$> run ge1

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
