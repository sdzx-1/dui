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
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

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
import SP.Eval (runLSPWithOutputs1)
import SP.SP (SP (..))
import SP.Type
import SP.BaseType
import SP.Util
import Shelly
import System.IO

type OutputType = String

data ChanNode
  = CN OutputType Int
  | SourceCN Int Int
  | TargetCN Int Int
  | CENUp OutputType Int
  | CENDown OutputType Int
  | EitherUpCN OutputType Int
  | EitherDownCN OutputType Int
  | TupleUpCn OutputType Int
  | TupleDownCn OutputType Int
  | BothUpCN OutputType Int
  | LoopEitherUpCN OutputType Int
  | LoopEitherDownCN OutputType Int
  | DynCN Int
  | DebugRtCN Int
  | Joint Int
  deriving (Show)

instance Eq ChanNode where
  a == b = chanNodeToInt a == chanNodeToInt b

instance Ord ChanNode where
  compare a b = compare (chanNodeToInt a) (chanNodeToInt b)

chanNodeToInt :: ChanNode -> Int
chanNodeToInt (CN _ i) = i
chanNodeToInt (SourceCN _ i) = i
chanNodeToInt (TargetCN _ i) = i
chanNodeToInt (CENUp _ i) = i
chanNodeToInt (CENDown _ i) = i
chanNodeToInt (EitherUpCN _ i) = i
chanNodeToInt (EitherDownCN _ i) = i
chanNodeToInt (TupleUpCn _ i) = i
chanNodeToInt (TupleDownCn _ i) = i
chanNodeToInt (BothUpCN _ i) = i
chanNodeToInt (LoopEitherUpCN _ i) = i
chanNodeToInt (LoopEitherDownCN _ i) = i
chanNodeToInt (Joint i) = i
chanNodeToInt (DynCN i) = i
chanNodeToInt (DebugRtCN i) = i

toName :: ChanNode -> String
toName = \case
  CN _ i -> show i
  SourceCN _ i -> show i
  TargetCN _ i -> show i
  CENUp _ i -> show i
  CENDown _ i -> show i
  EitherUpCN _ i -> show i
  EitherDownCN _ i -> show i
  TupleUpCn _ i -> show i
  TupleDownCn _ i -> show i
  BothUpCN _ i -> show i
  LoopEitherUpCN _ i -> show i
  LoopEitherDownCN _ i -> show i
  Joint i -> show i
  DynCN i -> show i
  DebugRtCN i -> show i

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
  ChanNode -> -- source
  ChanNode -> -- target
  ChanNode ->
  LSP xs i o ->
  m ChanNode
genGraph' source target i = \case
  Container _ lsp -> do
    k <- fresh
    source1 <- SourceCN k <$> fresh
    target1 <- TargetCN k <$> fresh
    addEdge @ChanNode (target1, source1)
    o <- genGraph' source1 target1 i lsp
    addEdge @ChanNode (source, target1)
    addEdge @ChanNode (source1, target)
    pure o
  v@(E _) -> do
    i1 <- CENUp (getLSPOutputTypeVal v) <$> fresh
    o1 <- CENDown (getLSPOutputTypeVal v) <$> fresh
    o <- CN (getLSPOutputTypeVal v) <$> fresh

    addEdge @ChanNode (source, i1)
    addEdge @ChanNode (o1, target)

    addEdge @ChanNode (i, i1)
    addEdge @ChanNode (i1, o1)
    addEdge @ChanNode (o1, o)
    pure o
  v@(L _) -> do
    i' <- CN (getLSPOutputTypeVal v) <$> fresh
    addEdge @ChanNode (i, i')
    pure i'
  a :>>> b -> do
    ai <- genGraph' source target i a
    genGraph' source target ai b
  a :+++ b -> do
    joint <- Joint <$> fresh
    let ait = getLSPInputTypeVal a
        bit = getLSPInputTypeVal b
    o1 <- EitherUpCN ait <$> fresh
    o2 <- EitherUpCN bit <$> fresh
    addEdge @ChanNode (i, joint)
    addEdge @ChanNode (joint, o1)
    addEdge @ChanNode (joint, o2)
    o1' <- genGraph' source target o1 a
    o2' <- genGraph' source target o2 b
    let aot = getLSPOutputTypeVal a
        bot = getLSPOutputTypeVal b
    ko <- EitherDownCN ("Either " ++ aot ++ " " ++ bot) <$> fresh
    addEdge @ChanNode (o1', ko)
    addEdge @ChanNode (o2', ko)
    pure ko
  LoopEither (lsp :: LSP xs (Either i' k') (Either o' k')) -> do
    let it = getLSPInputTypeVal lsp
    i1 <- LoopEitherUpCN it <$> fresh
    addEdge @ChanNode (i, i1)
    o1 <- genGraph' source target i1 lsp
    let ot = show $ typeOf @o' undefined
    leftO <- LoopEitherDownCN ot <$> fresh
    joint <- Joint <$> fresh
    addEdge @ChanNode (o1, joint)
    addEdge @ChanNode (joint, leftO)
    addEdge @ChanNode (joint, i1)
    pure leftO
  a :*** b -> do
    let ait = getLSPInputTypeVal a
        bit = getLSPInputTypeVal b
    o1 <- TupleUpCn ait <$> fresh
    o2 <- TupleUpCn bit <$> fresh
    joint <- Joint <$> fresh
    addEdge @ChanNode (i, joint)
    addEdge @ChanNode (joint, o1)
    addEdge @ChanNode (joint, o2)
    o1' <- genGraph' source target o1 a
    o2' <- genGraph' source target o2 b
    let aot = getLSPOutputTypeVal a
        bot = getLSPOutputTypeVal b
    ko <- TupleDownCn ("(" ++ aot ++ ", " ++ bot ++ ")") <$> fresh
    addEdge @ChanNode (o1', ko)
    addEdge @ChanNode (o2', ko)
    pure ko
  a :>>+ b -> do
    let ait = getLSPInputTypeVal a
    o1 <- BothUpCN ait <$> fresh
    o2 <- BothUpCN ait <$> fresh
    joint <- Joint <$> fresh
    addEdge @ChanNode (i, joint)
    addEdge @ChanNode (joint, o1)
    addEdge @ChanNode (joint, o2)
    genGraph' source target o1 a
    genGraph' source target o2 b
  Dyn -> do
    o <- DynCN <$> fresh
    addEdge @ChanNode (i, o)
    pure o
  DebugRt -> do
    o <- DebugRtCN <$> fresh
    addEdge @ChanNode (i, o)
    pure o

genGraph lsp =
  let itv = getLSPInputTypeVal lsp
   in fst $
        runIdentity $
          runState @(Graph ChanNode) (Vertex (CN itv 2)) $
            runFresh 3 $
              genGraph' (SourceCN 0 0) (TargetCN 0 1) (CN itv 2) lsp

renderLSP :: Typeable i => LSP xs i o -> String
renderLSP lsp =
  export
    (defaultStyle toName)
      { preamble = ["rankdir=LR"],
        vertexAttributes = \case
          EitherUpCN ot _ -> ["color" := "blue", "label" := remQ ot]
          EitherDownCN ot _ -> ["color" := "blue", "label" := remQ ot]
          TupleUpCn ot _ -> ["color" := "red", "label" := remQ ot]
          TupleDownCn ot _ -> ["color" := "red", "label" := remQ ot]
          BothUpCN ot _ -> ["color" := "green", "label" := remQ ot]
          LoopEitherUpCN ot _ -> ["color" := "purple", "label" := remQ ot]
          LoopEitherDownCN ot _ -> ["color" := "purple", "label" := remQ ot]
          Joint _ -> ["shape" := "point", "style" := "filled", "label" := "", "width" := "0", "height" := "0"]
          CN ot _ -> ["color" := "black", "label" := remQ ot]
          SourceCN i _ -> ["color" := "black", "label" := ("Event Source [" ++ show i ++ "]")]
          TargetCN i _ -> ["color" := "black", "label" := ("Picture Target [" ++ show i ++ "]")]
          CENUp ot _ -> ["color" := "black", "label" := (remQ ot ++ "|Event")]
          CENDown ot _ -> ["color" := "black", "label" := (remQ ot ++ "|Picture")]
          DynCN _ -> ["color" := "black", "label" := "{Dyn}"]
          DebugRtCN _ -> ["color" := "black", "label" := "{DebugRt}"],
        edgeAttributes = \x y -> case (x, y) of
          (_, EitherUpCN _ _) -> ["color" := "blue", "style" := "dashed", "label" := "E"]
          (_, EitherDownCN _ _) -> ["color" := "blue", "style" := "dashed", "label" := "E"]
          (_, TupleUpCn _ _) -> ["color" := "red", "style" := "dashed", "label" := "T"]
          (_, TupleDownCn _ _) -> ["color" := "red", "style" := "dashed", "label" := "T"]
          (_, BothUpCN _ _) -> ["color" := "green", "style" := "dashed", "label" := "B"]
          (_, LoopEitherUpCN _ _) -> ["color" := "purple", "style" := "dashed", "label" := "L"]
          (_, LoopEitherDownCN _ _) -> ["color" := "purple", "style" := "dashed", "label" := "L"]
          (_, Joint _) -> ["dir" := "none", "style" := "dashed"]
          (_, CN _ _) -> ["color" := "black"]
          (SourceCN _ _, _) -> ["color" := "blue"]
          (__, SourceCN _ _) -> ["color" := "black"]
          (_, TargetCN _ _) -> ["color" := "blue"]
          (_, CENUp _ _) -> ["color" := "black"]
          (_, CENDown _ _) -> ["color" := "orange"]
          (_, DynCN _) -> ["color" := "black"]
          (_, DebugRtCN _) -> ["color" := "black"],
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

te :: SP (Either Int Event) (Either Int Picture) ()
te = Get $ \case
  Left v -> Put (Left v) te
  Right Event -> Put (Right Picture) te

te' = Put (Right Picture) te

consp ::
  SP
    (Either (ChanIndex, Picture) Event)
    (Either (ChanIndex, Event) Picture)
    ()
consp = Get $ \case
  Left (_, Picture) -> Put (Right Picture) consp
  Right _ -> consp

-- >>> showLSP (lsp )
lsp =
  Container
    consp
    ( debug @"input"
        :>>> arrLSP (+ 1)
        :>>> debug @"+1"
        :>>> E te'
        :>>> arrLSPState 0 (\s a -> (s + a, s + a))
        :>>> E te'
        :>>> debug @"acc"
        :>>> E te'
        :>>> arrLSP ge
        :>>> debug @"generate Either"
        :>>> ((arrLSP (+ 1) :>>> debug @"el") ||| arrLSP (+ 2))
        :>>> debug @"modify Either"
        :>>> (arrLSP (* 2) &&& arrLSP id)
    )

-- >>> res
-- Just ({[1,2,3,4], [2,3,4,5], [2,5,9,14], [Right 2,Left 5,Left 9,Right 14], [6,10], [4,6,16,10]},[(ChanIndex 93,Picture),(ChanIndex 93,Picture),(ChanIndex 93,Picture)],[(8,4),(12,6),(32,16),(20,10)])
res = runLSPWithOutputs1 [1 .. 4] lsp

vs :: [Int]
vs = [1, 2, 4]

cvsp :: [Int] -> SP Int (Either [Int] Int) ()
cvsp xs = Get $ \x ->
  if x `elem` vs
    then Put (Left $ reverse (x : xs)) $ cvsp []
    else Put (Right x) $ cvsp (x : xs)

-- >>> showLSP (lp :>>+ lp  )
-- >>> runLSPWithOutputs [10] lp
lp =
  LoopEither
    ( arrLSP bothC
        :>>> debug @"v1"
        :>>> arrLSP ge
        :>>> ( (arrLSP (\x -> x * 3 + 1) :>>> debug @"v2")
                 ||| arrLSP (`div` 2)
             )
        :>>> L (cvsp [])
    )
