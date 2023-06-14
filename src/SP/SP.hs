module SP.SP where

import Control.Monad ((<=<))

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
