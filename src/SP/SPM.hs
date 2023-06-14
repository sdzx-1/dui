{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MonoLocalBinds #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeApplications #-}

module SP.SPM where

import Control.Algebra (Has)
import Control.Carrier.State.Strict (State, runState)
import Control.Effect.Labelled (HasLabelledLift, lift, runLabelledLift)
import qualified Control.Effect.State as S
import Control.Monad (forever, (<=<))

data SP i o a
  = Get (i -> SP i o a)
  | Put o (SP i o a)
  | Return a

instance Functor (SP i o) where
  fmap f (Get fun) = Get (fmap f . fun)
  fmap f (Put o sp) = Put o (fmap f sp)
  fmap f (Return a) = Return (f a)

instance Applicative (SP i o) where
  f <*> a = do
    f' <- f
    f' <$> a
  pure = Return

instance Monad (SP i o) where
  (Get fun) >>= f = Get (f <=< fun)
  (Put o sp) >>= f = Put o (sp >>= f)
  (Return a) >>= f = f a

get ::
  HasLabelledLift (SP i o) sig m => m i
get = lift (Get Return)

put ::
  HasLabelledLift (SP i o) sig m => o -> m ()
put o = lift (Put o (Return ()))

example ::
  ( Has (State Int) sig m,
    HasLabelledLift (SP Bool String) sig m
  ) =>
  m ()
example = do
  put "init"
  put "loop start"
  forever $ do
    b <- get
    S.modify @Int (+ 1)
    i <- S.get @Int
    put (show (b, i))

runExample =
  runLabelledLift $
    runState @Int 0 example

eval :: (Show o, Read i) => SP i o a -> IO ()
eval (Return _) = pure ()
eval (Get f) = do
  putStrLn "get val"
  st <- getLine
  eval $ f (read st)
eval (Put o sp) = do
  putStrLn $ "output: " ++ show o
  eval sp
