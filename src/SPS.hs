{-# LANGUAGE GADTs #-}

module SPS where

import SP

data SPS i o where
  SPL :: SP i o -> SPS i o
  (:>>>) :: SPS i o -> SPS o j -> SPS i j
  (:+++) :: SPS i o -> SPS m n -> SPS (Either i m) (Either o n)
  (:|||) :: SPS i o -> SPS m o -> SPS (Either i m) o

-- newtype Chan a = Chan (Seq a)

-- -- >>> [t, t1, t2]
-- -- [fromList [1,2,3,4],fromList [1,2,3,4,5],fromList [0,1,2,3,4]]
-- t = Seq.fromList [1, 2, 3, 4]
-- t1 = t |> 5
-- t1' =
--   let a :<| _ = t
--    in a
-- t2 = 0 <| t
