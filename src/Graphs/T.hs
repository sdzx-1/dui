{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}

module Graphs.T where

import Control.Algebra (Has, (:+:))
import Control.Carrier.Fresh.Strict (runFresh)
import Control.Carrier.State.Strict (runState)
import Control.Effect.Fresh (Fresh)
import Control.Effect.State (State)
import Control.Monad (forM, forM_, unless, when)
import Control.Monad.IO.Class
import Data.Foldable (foldl')
import Data.IORef
import Data.Kind (Type)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Proxy (Proxy (..))
import qualified Data.Text as T
import Data.Vector.Storable (fromList)
import Foreign.C (CInt)
import GHC.Exts (IsList (toList))
import Graphs.R
import SDL hiding (Event)
import qualified SDL.Font
import qualified SDL.Framerate
import qualified SDL.Primitive
import SP.BaseType
import qualified SP.BaseType as B
import SP.Eval
import SP.Gen
import SP.Type
import SP.Util
import Unsafe.Coerce (unsafeCoerce)

red :: SDL.Primitive.Color
red = V4 255 50 50 255

green :: SDL.Primitive.Color
green = V4 50 255 50 255

blue :: SDL.Primitive.Color
blue = V4 50 50 255 255

black :: SDL.Primitive.Color
black = V4 0 0 0 255

white :: SDL.Primitive.Color
white = V4 255 255 255 255

main ::
  forall xs i o.
  ( SomeValsToHList xs,
    All Show xs,
    Show o
  ) =>
  [i] ->
  LSP xs i o ->
  IO ()
main ls lsp = do
  initialize [InitVideo]
  SDL.Font.initialize
  font <- SDL.Font.load "data/fonts/SourceCodePro-Regular.otf" 20
  window <-
    createWindow
      "My SDL Application"
      defaultWindow
        { windowInitialSize = V2 2000 1000
        }
  renderer <- createRenderer window (-1) defaultRenderer
  showWindow window
  let fps = 30 :: Int
  SDL.Framerate.with fps $ \x -> do
    runState @EvalState (initEvalState ls) $
      runState @DynMap Map.empty $
        runFresh 2 $ do
          gres <- genES' (intToChanIndex 0) (intToChanIndex 1) lsp
          loopFor @xs @o renderer font x gres
  destroyWindow window
  quit

loopFor ::
  forall (xs :: [Type]) o sig m.
  ( Has (State EvalState :+: State DynMap :+: Fresh) sig m,
    MonadFail m,
    MonadIO m,
    All Show xs,
    SomeValsToHList xs,
    Show o
  ) =>
  SDL.Renderer ->
  SDL.Font.Font ->
  SDL.Framerate.Manager ->
  GenResult ->
  m ()
loopFor r font fpsm genResult = do
  mpsRef <- liftIO $ newIORef (V2 0 0 :: V2 CInt)
  cpmRef <- liftIO $ newIORef Map.empty
  loop' mpsRef cpmRef genResult
  where
    loop' ::
      (Has (State EvalState :+: State DynMap :+: Fresh) sig m, MonadFail m, MonadIO m) =>
      IORef (V2 CInt) ->
      IORef (Map ChanIndex Picture) ->
      GenResult ->
      m ()
    loop' mpsRef cpmRef gr@GenResult {allBFCI, lspOI} = do
      eval
      outputSomeValList <- forM allBFCI $ \i -> takeChanAll i
      let nsv = someValsToHList @xs outputSomeValList
      liftIO $ putStrLn "all outputs:"
      liftIO $ print nsv

      os <- toList <$> takeChanAll lspOI
      let os' = map (\(SomeVal a) -> unsafeCoerce @_ @o a) os
      liftIO $ putStrLn "o:"
      liftIO $ print os'

      chan0 <- toList <$> takeChanAll (ChanIndex 0)
      let chan0' = map (\(SomeVal a) -> unsafeCoerce @_ @(ChanIndex, Picture) a) chan0

      liftIO $ putStrLn "chan0, pictures:"
      liftIO $ print chan0'

      forM_ chan0' $ \(ci, p) -> liftIO $ modifyIORef' cpmRef (Map.insert ci p)

      -----------------------
      events <- liftIO pollEvents
      let eventIsQPress event =
            case eventPayload event of
              KeyboardEvent keyboardEvent ->
                keyboardEventKeyMotion keyboardEvent == Pressed
                  && keysymKeycode (keyboardEventKeysym keyboardEvent) == KeycodeQ
              QuitEvent -> True
              _ -> False
          qPressed = any eventIsQPress events

          mpos v2 event =
            case eventPayload event of
              MouseMotionEvent (MouseMotionEventData _ _ _ (P v2') _) -> fmap fromIntegral v2'
              _ -> v2

          createEvent event =
            case eventPayload event of
              MouseButtonEvent (MouseButtonEventData _ Pressed _ ButtonLeft _ (P (V2 x y))) ->
                [B.Event (LClick (Point (fromIntegral x) (fromIntegral y)))]
              MouseMotionEvent (MouseMotionEventData _ _ [ButtonLeft] _ (V2 x y)) ->
                [B.Event $ Drag (fromIntegral x) (fromIntegral y)]
              _ -> []

      let allEvent = concatMap createEvent events
      cpm <- liftIO $ readIORef cpmRef
      let keys = Map.keys cpm
      forM_ keys $ \key -> do
        forM_ allEvent $ \evt -> writeVal (SomeVal $ Right evt) key

      mpos0 <- liftIO $ readIORef mpsRef
      liftIO $ writeIORef mpsRef (foldl' mpos mpos0 events)

      mpos' <- liftIO $ readIORef mpsRef

      -- Clear the screen!
      SDL.rendererDrawColor r $= black
      SDL.clear r

      -- render picture
      SDL.rendererDrawColor r $= white
      -- liftIO $ render r font examplePicture
      cpm <- liftIO $ readIORef cpmRef
      let ps = Map.elems cpm
      liftIO $ render r font (Picture (Rect 0 0 1000 1000) (LPictures ps))

      SDL.present r
      SDL.Framerate.delay_ fpsm -- Delay to keep framerate constant.
      unless qPressed (loop' mpsRef cpmRef gr)
