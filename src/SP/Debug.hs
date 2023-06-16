{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}

module SP.Debug where

import Algebra.Graph (Graph (Vertex))
import qualified Algebra.Graph as G
import Algebra.Graph.Export.Dot
import Control.Algebra (Has, (:+:))
import Control.Carrier.Fresh.Strict (Fresh, fresh, runFresh)
import Control.Carrier.State.Strict (State, modify, runState)
import Data.Functor.Identity
import qualified Data.Text as T
import Data.Typeable (Typeable, typeOf)
import GHC.TypeLits (KnownSymbol, Symbol)
import SP.Gen (runLSPWithOutputs)
import SP.SP (SP (..))
import SP.Type
import SP.Util
import Shelly
import System.IO

type OutputType = String

data ChanNode
  = CN OutputType Int
  | EitherUpCN Int
  | EitherDownCN Int
  | TupleUpCn Int
  | TupleDownCn Int
  | BothUpCN Int
  | LoopEitherUpCN Int
  | LoopEitherDownCN Int
  | Joint Int

instance Eq ChanNode where
  a == b = chanNodeToInt a == chanNodeToInt b

instance Ord ChanNode where
  compare a b = compare (chanNodeToInt a) (chanNodeToInt b)

chanNodeToInt :: ChanNode -> Int
chanNodeToInt (CN _ i) = i
chanNodeToInt (EitherUpCN i) = i
chanNodeToInt (EitherDownCN i) = i
chanNodeToInt (TupleUpCn i) = i
chanNodeToInt (TupleDownCn i) = i
chanNodeToInt (BothUpCN i) = i
chanNodeToInt (LoopEitherUpCN i) = i
chanNodeToInt (LoopEitherDownCN i) = i
chanNodeToInt (Joint i) = i

instance Show ChanNode where
  show = \case
    CN it i -> remQ it ++ ", " ++ show i
    EitherUpCN i -> show i
    EitherDownCN i -> show i
    TupleUpCn i -> show i
    TupleDownCn i -> show i
    BothUpCN i -> show i
    LoopEitherUpCN i -> show i
    LoopEitherDownCN i -> show i
    Joint i -> show i

remQ :: String -> String
remQ [] = []
remQ ('"' : xs) = remQ xs
remQ (x : xs) = x : remQ xs

addVertex :: forall a sig m. Has (State (Graph a)) sig m => a -> m ()
addVertex a = modify @(Graph a) (G.vertex a `G.overlay`)

addEdge :: forall a sig m. Has (State (Graph a)) sig m => (a, a) -> m ()
addEdge (a, b) = modify @(Graph a) ((G.vertex a `G.connect` G.Vertex b) `G.overlay`)

getLSPInputTypeVal :: forall xs i o. Typeable i => LSP xs i o -> String
getLSPInputTypeVal _ = show $ typeOf @i undefined

getLSPOutputTypeVal :: forall xs i o. Typeable o => LSP xs i o -> String
getLSPOutputTypeVal _ = show $ typeOf @o undefined

genGraph' ::
  Has (Fresh :+: State (Graph ChanNode)) sig m =>
  ChanNode ->
  LSP xs i o ->
  m ChanNode
genGraph' i = \case
  v@(E _) -> do
    i' <- CN (getLSPOutputTypeVal v) <$> fresh
    addEdge @ChanNode (i, i')
    pure i'
  a :>>> b -> do
    ai <- genGraph' i a
    genGraph' ai b
  a :+++ b -> do
    joint <- Joint <$> fresh
    o1 <- EitherUpCN <$> fresh
    o2 <- EitherUpCN <$> fresh
    addEdge @ChanNode (i, joint)
    addEdge @ChanNode (joint, o1)
    addEdge @ChanNode (joint, o2)
    o1' <- genGraph' o1 a
    o2' <- genGraph' o2 b
    ko <- EitherDownCN <$> fresh
    addEdge @ChanNode (o1', ko)
    addEdge @ChanNode (o2', ko)
    pure ko
  LoopEither lsp -> do
    i1 <- LoopEitherUpCN <$> fresh
    addEdge @ChanNode (i, i1)
    o1 <- genGraph' i1 lsp
    leftO <- LoopEitherDownCN <$> fresh
    joint <- Joint <$> fresh
    addEdge @ChanNode (o1, joint)
    addEdge @ChanNode (joint, leftO)
    addEdge @ChanNode (joint, i1)
    pure leftO
  a :*** b -> do
    o1 <- TupleUpCn <$> fresh
    o2 <- TupleUpCn <$> fresh
    joint <- Joint <$> fresh
    addEdge @ChanNode (i, joint)
    addEdge @ChanNode (joint, o1)
    addEdge @ChanNode (joint, o2)
    o1' <- genGraph' o1 a
    o2' <- genGraph' o2 b
    ko <- TupleDownCn <$> fresh
    addEdge @ChanNode (o1', ko)
    addEdge @ChanNode (o2', ko)
    pure ko
  a :>>+ b -> do
    o1 <- BothUpCN <$> fresh
    o2 <- BothUpCN <$> fresh
    joint <- Joint <$> fresh
    addEdge @ChanNode (i, joint)
    addEdge @ChanNode (joint, o1)
    addEdge @ChanNode (joint, o2)
    genGraph' o1 a
    genGraph' o2 b

genGraph lsp =
  let itv = getLSPInputTypeVal lsp
   in fst $
        runIdentity $
          runState @(Graph ChanNode) (Vertex (CN itv 0)) $
            runFresh 1 $
              genGraph' (CN itv 0) lsp

renderLSP :: Typeable i => LSP xs i o -> String
renderLSP lsp =
  export
    defaultStyleViaShow
      { preamble = ["rankdir=LR"],
        vertexAttributes = \case
          EitherUpCN _ -> ["color" := "blue"]
          EitherDownCN _ -> ["color" := "blue"]
          TupleUpCn _ -> ["color" := "red"]
          TupleDownCn _ -> ["color" := "red"]
          BothUpCN _ -> ["color" := "green"]
          LoopEitherUpCN _ -> ["color" := "purple"]
          LoopEitherDownCN _ -> ["color" := "purple"]
          Joint _ -> ["shape" := "point", "style" := "filled", "label" := "", "width" := "0", "height" := "0"]
          _ -> ["color" := "black"],
        edgeAttributes = \x y -> case (x, y) of
          (_, EitherUpCN _) -> ["color" := "blue", "style" := "dashed", "label" := "E"]
          (_, EitherDownCN _) -> ["color" := "blue", "style" := "dashed", "label" := "E"]
          (_, TupleUpCn _) -> ["color" := "red", "style" := "dashed", "label" := "T"]
          (_, TupleDownCn _) -> ["color" := "red", "style" := "dashed", "label" := "T"]
          (_, BothUpCN _) -> ["color" := "green", "style" := "dashed", "label" := "B"]
          (_, LoopEitherUpCN _) -> ["color" := "purple", "style" := "dashed", "label" := "L"]
          (_, LoopEitherDownCN _) -> ["color" := "purple", "style" := "dashed", "label" := "L"]
          (_, Joint _) -> ["dir" := "none", "style" := "dashed"]
          _ -> ["color" := "black"],
        defaultVertexAttributes = ["shape" := "plaintext"]
      }
    (genGraph lsp)

showLSP :: Typeable i => LSP xs i o -> IO ()
showLSP lsp = do
  hSetBuffering stdout LineBuffering
  shelly $ verbosely $ do
    let dotName = "/tmp/lsp.dot"
        pngName = "/tmp/lsp.png"
    liftIO $ writeFile dotName $ renderLSP lsp
    run_ "dot" ["-Tpng", "-o", pngName, T.pack dotName]
    run_ "eog" [pngName]

----------------------------- example
newtype DebugVal (st :: Symbol) = Val String

instance Show (DebugVal s) where
  show (Val v) = v

debug :: forall (s :: Symbol) i. (Typeable i, Show i, KnownSymbol s) => LSP '[DebugVal s] i i
debug = arrLSP (Val @s . show) :>>+ arrLSP id

ge :: Int -> Either Int Int
ge i = if odd i then Left i else Right i

lsp =
  debug @"input"
    :>>> arrLSP (+ 1)
    :>>> debug @"+1"
    :>>> arrLSPState 0 (\s a -> (s + a, s + a))
    :>>> debug @"acc"
    :>>> arrLSP ge
    :>>> debug @"generate Either"
    :>>> ((arrLSP (+ 1) :>>> debug @"el") ||| arrLSP (+ 2))
    :>>> debug @"modify Either"
    :>>> (arrLSP (* 2) &&& arrLSP id)

-- >>> res
-- >>> showLSP (lsp)
-- Just ({[1,2,3,4], [2,3,4,5], [2,5,9,14], [Right 2,Left 5,Left 9,Right 14], [6,10], [4,6,16,10]},[(8,4),(12,6),(32,16),(20,10)])
res = runLSPWithOutputs [1 .. 4] lsp

vs :: [Int]
vs = [1, 2, 4]

cvsp :: [Int] -> SP Int (Either [Int] Int) ()
cvsp xs = Get $ \x ->
  if x `elem` vs
    then Put (Left $ reverse (x : xs)) $ cvsp []
    else Put (Right x) $ cvsp (x : xs)

-- >>> showLSP (lp &&& lp &&& lp)
-- >>> runLSPWithOutputs [10] lp
-- Just ({[10,5,16,8], [16]},[[5,16,8,4]])
lp =
  LoopEither
    ( arrLSP bothC
        :>>> debug @"v1"
        :>>> arrLSP ge
        :>>> ( (arrLSP (\x -> x * 3 + 1) :>>> debug @"v2")
                 ||| arrLSP (`div` 2)
             )
        :>>> E (cvsp [])
    )
