module SP.ESP where

import Control.Monad ((<=<))

data Event = Event

data Picture = Picture

data ESP i o a
  = Get (Either i Event -> ESP i o a)
  | Put (Either o Picture) (ESP i o a)
  | Return a

instance Functor (ESP i o) where
  fmap f (Get fun) = Get (fmap f . fun)
  fmap f (Put o esp) = Put o (fmap f esp)
  fmap f (Return a) = Return (f a)

instance Applicative (ESP i o) where
  f <*> a = do
    f' <- f
    f' <$> a
  pure = Return

instance Monad (ESP i o) where
  (Get fun) >>= f = Get (f <=< fun)
  (Put o esp) >>= f = Put o (esp >>= f)
  (Return a) >>= f = f a
