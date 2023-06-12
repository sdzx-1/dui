{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

module SP.LSPBranch where

import Data.Kind (Constraint)
import GHC.TypeLits (ErrorMessage (..), TypeError)

data SP i o
  = Get (i -> SP i o)
  | Put o (SP i o)

type family Reverse' (a :: [xs]) (b :: [xs]) :: [xs] where
  Reverse' '[] ys = ys
  Reverse' (x ': xs) ys = Reverse' xs (x ': ys)

type family (:++:) (a :: [xs]) (b :: [xs]) :: [xs] where
  xs :++: ys = Reverse' (Reverse' xs '[]) ys

data (a :: [xs]) >+ b

type family CreateErrorMessage a b c :: ErrorMessage where
  CreateErrorMessage a b c =
    Text "Left ouput: " :<>: ShowType a
      :$$: Text "Right input: " :<>: ShowType b
      :$$: Text "Error: " :<>: ShowType c :<>: Text " /= " :<>: ShowType b

type family SpecialEQ a b :: Constraint where
  SpecialEQ (_ >+ o) o = ()
  SpecialEQ o o = ()
  SpecialEQ (a >+ a') b = TypeError (CreateErrorMessage (a >+ a') b a')
  SpecialEQ a b = TypeError (CreateErrorMessage a b a)

type family Connect a b where
  Connect (a1 >+ _) (b1 >+ b2) = (a1 :++: b1) >+ b2
  Connect a (b1 >+ b2) = b1 >+ b2
  Connect (a1 >+ _) b = a1 >+ b
  Connect a b = b

type family MegerEither l r where
  MegerEither (ls >+ l) (rs >+ r) = (ls :++: rs) >+ Either l r
  MegerEither l (rs >+ r) = rs >+ Either l r
  MegerEither (ls >+ l) r = ls >+ Either l r
  MegerEither l r = Either l r

type family MegerBoth l r where
  MegerBoth (ls >+ l) (rs >+ r) = (ls :++: rs) >+ (l, r)
  MegerBoth l (rs >+ r) = rs >+ (l, r)
  MegerBoth (ls >+ l) r = ls >+ (l, r)
  MegerBoth l r = (l, r)

type family Generate a b where
  Generate (xs >+ a) (ys >+ b) = (xs :++: (a ': ys)) >+ b
  Generate a (ys >+ b) = (a ': ys) >+ b
  Generate (xs >+ a) b = (xs :++: '[a]) >+ b
  Generate a b = '[a] >+ b

data LSP i o where
  E :: SP i o -> LSP i o
  (:>>>) :: SpecialEQ o o' => LSP i o -> LSP o' p -> LSP i (Connect o p)
  (:+++) :: LSP i1 o1 -> LSP i2 o2 -> LSP (Either i1 i2) (MegerEither o1 o2)
  (:***) :: LSP i1 o1 -> LSP i2 o2 -> LSP (i1, i2) (MegerBoth o1 o2)
  (:>+) :: LSP i o1 -> LSP i o2 -> LSP i (Generate o1 o2)

---------- example
-- >>> :t (pk :>>> pk2)
-- (pk :>>> pk2) :: LSP Int ('[Float] >+ Int)

pk :: LSP Int Bool -- (WithOutput '[Int] Int)
pk = undefined

pk1 :: LSP Int ('[Bool] >+ Int)
pk1 = undefined

pk2 :: LSP Int ('[Float] >+ Int)
pk2 = undefined

pk3 :: LSP Int ('[Double] >+ Int)
pk3 = undefined

pkn1 = pk :>+ pk

pkn2 =
  pk1
    :>>> pk2
    :>>> pk3
