{-# LANGUAGE LambdaCase #-}

module Graphs.R where

import qualified Data.Text as T
import SDL hiding (Point)
import SDL.Font (Font, solid)
import SP.BaseType

render' :: Point -> Renderer -> Font -> Picture -> IO ()
render' (Point x0 y0) r font (Picture (Rect x y w h) lp) = do
  let (x1, y1) = (x0 + x, y0 + y)
  drawRect r (Just $ Rectangle (P (V2 (floor x1) (floor y1))) (V2 (floor w) (floor h)))
  case lp of
    LRect (Rect x2 y2 w1 h1) -> do
      let (x3, y3) = (x1 + x2, y1 + y2)
      fillRect r (Just $ Rectangle (P (V2 (floor x3) (floor y3))) (V2 (floor w1) (floor h1)))
    LPictures ls -> mapM_ (render' (Point x1 y1) r font) ls
    LString st -> renderString r font st (Point x1 y1)

render :: Renderer -> Font -> Picture -> IO ()
render = render' (Point 0 0)

examplePicture :: Picture
examplePicture =
  Picture
    (Rect 10 20 500 500)
    ( LPictures
        [ Picture (Rect 3 4 55 22) (LRect $ Rect 0 0 50 20)
        , Picture (Rect 0 300 100 30) (LString "hello")
        , Picture (Rect 0 340 100 30) (LString "sdzx-1")
        ]
    )

renderString :: Renderer -> SDL.Font.Font -> String -> Point -> IO ()
renderString r font st (Point x y) = do
  surf <- SDL.Font.solid font (V4 255 50 50 255) (T.pack st)
  text <- createTextureFromSurface r surf
  freeSurface surf
  TextureInfo _ _ w h <- queryTexture text
  copy
    r
    text
    Nothing
    (Just $ Rectangle (P (V2 (floor x) (floor y))) (V2 w h))
  destroyTexture text