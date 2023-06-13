{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE GADTs #-}
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
import SP.Gen
import SP.Type
import SP.Util
import Shelly
import System.IO

addVertex :: forall a sig m. Has (State (Graph a)) sig m => a -> m ()
addVertex a = modify @(Graph a) (G.vertex a `G.overlay`)

addEdge :: forall a sig m. Has (State (Graph a)) sig m => (a, a) -> m ()
addEdge (a, b) = modify @(Graph a) ((G.vertex a `G.connect` G.Vertex b) `G.overlay`)

genGraph' ::
  Has (Fresh :+: State (Graph Int)) sig m =>
  Int ->
  LSP xs i o ->
  m Int
genGraph' i = \case
  E _ -> do
    i' <- fresh
    addEdge @Int (i, i')
    pure i'
  a :>>> b -> do
    ai <- genGraph' i a
    genGraph' ai b
  a :+++ b -> do
    o1 <- fresh
    o2 <- fresh
    addEdge @Int (i, o1)
    addEdge @Int (i, o2)
    o1' <- genGraph' o1 a
    o2' <- genGraph' o2 b
    ko <- fresh
    addEdge @Int (o1', ko)
    addEdge @Int (o2', ko)
    pure ko
  a :*** b -> do
    o1 <- fresh
    o2 <- fresh
    addEdge @Int (i, o1)
    addEdge @Int (i, o2)
    o1' <- genGraph' o1 a
    o2' <- genGraph' o2 b
    ko <- fresh
    addEdge @Int (o1', ko)
    addEdge @Int (o2', ko)
    pure ko
  a :>>+ b -> do
    o1 <- fresh
    o2 <- fresh
    addEdge @Int (i, o1)
    addEdge @Int (i, o2)
    genGraph' o1 a
    genGraph' o2 b

genGraph lsp =
  fst $
    runIdentity $
      runState @(Graph Int) (Vertex 0) $
        runFresh 1 $
          genGraph' 0 lsp

renderLSP :: LSP xs i o -> String
renderLSP lsp =
  export
    defaultStyleViaShow
      { preamble = ["rankdir=LR"]
      -- , defaultVertexAttributes = ["shape" := "plaintext"]
      }
    (genGraph lsp)

showLSP :: LSP xs i o -> IO ()
showLSP lsp = do
  hSetBuffering stdout LineBuffering
  shelly $ verbosely $ do
    liftIO $ writeFile "lsp.dot" $ renderLSP lsp
    run_ "dot" ["-Tpng", "-o", "lsp.png", "lsp.dot"]
    run_ "eog" ["lsp.png"]

----------------------------- example
ge :: Int -> Either Int Int
ge i = if odd i then Left i else Right i

-- >>> show lsp
-- >>> res
-- >>> runLSPWithOutputs [1..10] lsp
-- "* -> ((*) :>+ (* -> * -> * -> ((*) +++ (* -> * -> * -> ((*) +++ (*)) -> *)) -> * -> * -> ((* -> ((*) :>+ (*))) *** (* -> ((*) *** (*)))) -> ((*) :>+ (*))))"
-- Just [2,4,6,8,10]
-- Just ({["2","3","4","5","6","7","8","9","10","11"], ["-2","-4","-6","-8","-10"], ["(2,(3,3))","(4,(5,5))","(6,(7,7))","(8,(9,9))","(10,(11,11))"]},[2,4,6,8,10])
res = runLSP [1 .. 10] lsp

-- >>> showLSP lsp
lsp =
  arrLSP (+ 1)
    :>>> ( arrLSP show
             :>>+ ( arrLSPState 0 (\s a -> (s + a, s + a))
                      :>>> arrLSPState 0 (\s a -> (a, a - s))
                      :>>> arrLSP ge
                      :>>> ( arrLSP id
                               ||| ( arrLSP (* (-1))
                                       :>>> arrLSP id
                                       :>>> arrLSP ge
                                       :>>> (arrLSP id ||| arrLSP id)
                                   )
                           )
                      :>>> ( ( filterLSP (< 0)
                                 :>>> ( arrLSP show
                                          :>>+ arrLSP abs
                                      )
                             )
                               &&& filterLSP (> 0)
                               &&& filterLSP (> 0)
                           )
                      :>>> ( arrLSP show
                               :>>+ arrLSP fst
                           )
                  )
         )
