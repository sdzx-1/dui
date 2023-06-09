{-# OPTIONS_GHC -Wno-incomplete-patterns #-}

module SPM where

data SP i o m a
  = Get (i -> SP i o m a)
  | Put o (SP i o m a)
  | Eff (m (SP i o m a))
  | Return a

instance (Functor m) => Functor (SP i o m) where
  fmap f (Get fun) = Get (fmap f . fun)
  fmap f (Put o sp) = Put o (fmap f sp)
  fmap f (Eff msp) = Eff (fmap (fmap f) msp)
  fmap f (Return a) = Return (f a)

instance (Functor m) => Applicative (SP i o m) where
  pure a = Return a
  (<*>) = undefined

instance (Functor m) => Monad (SP i o m) where
  (Get fun) >>= f = Get ((>>= f) . fun)
  (Put o sp) >>= f = Put o (sp >>= f)
  (Eff msp) >>= f = Eff (fmap (>>= f) msp)
  (Return a) >>= f = f a

get :: SP i o m i
get = Get Return

put :: o -> SP i o m ()
put o = Put o (Return ())

eff :: (Functor m) => m a -> SP i o m a
eff ma = Eff (fmap Return ma)

t1 :: SP Int Bool IO ()
t1 = do
  input <- get
  eff $ print input
  put True
  pure ()
  eff $ do
    print 1
    print input
