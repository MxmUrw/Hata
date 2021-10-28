
{-# LANGUAGE OverloadedStrings, OverloadedLabels, ImplicitParams, PatternSynonyms #-}

module Hata.Runtime.UI.EditorMain where


-- original author:
--    Mirco "MacSlow" Mueller <macslow@bangang.de>
--
-- created:
--    10.1.2006 (or so)
--
-- http://www.gnu.org/licenses/licenses.html#GPL
--
-- ported to Haskell by:
--    Duncan Coutts <duncan.coutts@worc.ox.ac.uk>
--
-- updated to GTK 3 by Catherine Holloway
-- converted to Haskell GI by Kilian Kilger
--

import qualified GI.Cairo
import qualified GI.Gdk as GDK
import qualified GI.Gtk as GTK
-- import qualified GI.Gdk.Objects.Window as GDK
-- import GI.GLib (pattern PRIORITY_DEFAULT, timeoutAdd)
import GI.GLib -- (PRIORITY_DEFAULT, timeoutAdd)
import GI.Cairo.Render.Connector (renderWithContext)
import GI.Cairo.Render
import GI.Cairo.Render.Types
import qualified GI.Cairo.Render.Internal as Internal
import Data.Time
import Control.Monad (when)
import Data.Maybe (isJust)
import Data.IORef
import Data.Text as Text
import Data.Maybe (fromMaybe)
import Data.HashMap.Strict as H

import Hata.Runtime.Application.Render.Definition
import qualified GI.Cairo.Render.Types as Internal


-- from example
import Control.Monad (void)
import System.Environment (getArgs, getProgName)

import Data.Int (Int32)

import qualified GI.Gtk as Gtk
import Data.GI.Base
import Data.GI.Base.ShortPrelude
import Data.GI.Base.Attributes
import GI.Gtk.Enums (PropagationPhase(PropagationPhaseCapture))

type DrawState = HashMap Text Extent



----------------------------------------------
-- drawing

setCairoState :: BaseItem -> Render ()
setCairoState (StringBI (RGB r g b) size s) = do
  selectFontFace ("MxFont" :: Text) FontSlantNormal FontWeightNormal
  setSourceRGB (fromIntegral r / 255) (fromIntegral g / 255) (fromIntegral b / 255)
  setFontSize (fromIntegral size)
setCairoState (RectangleBI (RGB r g b) size) = do
  setSourceRGB (fromIntegral r / 255) (fromIntegral g / 255) (fromIntegral b / 255)

renderItem :: Item -> Render ()
renderItem (Item loc a) = do
  save
  setCairoState a
  render a
  restore
    where (x,y) = fromRationalCoord loc
          render (StringBI _ _ s) = do
              moveTo x y
              showText s
          render (RectangleBI _ s) = do
            let (w,h) = fromRationalCoord s
            rectangle x y w h
            fill

computeExtent :: BaseItem -> Render (Extent)
computeExtent (StringBI _ _ s) = do
  ex <- textExtents s
  let (x,y) = (textExtentsXadvance ex , textExtentsYadvance ex)
  return $ toRationalCoord (x,y)
computeExtent (RectangleBI _ s) = pure s

stateCommand :: GTK.IsWidget widget => widget
             -> IORef DrawState
             -> StateCmd Text BaseItem
             -> Render ()
stateCommand canvas drawRef ClearAll = liftIO $ modifyIORef' drawRef (\_ -> H.empty)
stateCommand canvas drawRef (Clear n) = liftIO $ modifyIORef' drawRef (H.delete n)
stateCommand canvas drawRef (Set n x) = do

  -- We compute the extent of an item
  save
  setCairoState x
  ex <- computeExtent x
  restore

  -- We save the extent in the hashmap
  liftIO $ modifyIORef' drawRef (H.insert n ex)


drawCommand :: GTK.IsWidget widget => widget
             -> IORef DrawState
             -> Cmd
             -> Render ()
drawCommand canvas drawRef (DoChangeState scmd) = stateCommand canvas drawRef scmd
drawCommand canvas drawRef (DoRender getItems) = do

  width  <- liftIO $ GTK.widgetGetAllocatedWidth  canvas
  height <- liftIO $ GTK.widgetGetAllocatedHeight canvas

  drawState <- liftIO $ readIORef drawRef
  let items = getItems (\a -> case drawState !? a of
                           Just x -> Right x
                           Nothing -> Left ())
                       (((fromIntegral width,1),(fromIntegral height,1)))
  mapM renderItem items
  return ()

drawCommands :: GTK.IsWidget widget => widget
             -> IORef DrawState
             -> IORef a -> (a -> [Cmd])
             -> Render Bool
drawCommands canvas drawStateRef stateRef getCmds = do

  state <- liftIO $ readIORef stateRef
  let cmds = getCmds state
  mapM (drawCommand canvas drawStateRef) cmds

  return True








---------------------------------------------------------
-- main


initialSize :: Int
initialSize = 256







activate :: (forall widget. GTK.IsWidget widget => widget -> Render Bool)
     -> (Text -> IO ())
     -> Gtk.Application -> IO ()
activate renderer keyhandler app = do

  GTK.init

  canvas <- GTK.drawingAreaNew

  window <- new Gtk.ApplicationWindow [#application := app,
                                       #title := "Hata Editor",
                                       #child := canvas]

  -- GTK.windowSetPosition window GTK.WindowPositionCenterAlways

  -- GTK.widgetSetAppPaintable window True

  GTK.windowSetDefaultSize window (fromIntegral initialSize)
                                  (fromIntegral initialSize)

  {-
  geometry <- GDK.newZeroGeometry
  GDK.setGeometryMaxWidth  geometry 512
  GDK.setGeometryMaxHeight geometry 512
  GDK.setGeometryMinWidth  geometry 32
  GDK.setGeometryMinHeight geometry 32
  GDK.setGeometryMinAspect geometry 1
  GDK.setGeometryMaxAspect geometry 1

  GTK.windowSetGeometryHints window (Just window) (Just geometry) []
-}


  let myhandle :: Word32 -> Word32 -> [GDK.ModifierType] -> IO Bool
      myhandle = \keyval keycode state -> do
        name <- Gtk.acceleratorName keyval state
        case Text.unpack name of
          -- "Escape" -> do GTK.mainQuit
          --                return True
          _        -> keyhandler name >> GTK.widgetQueueDraw canvas >> return True
        return True


  {-
  GTK.onWidgetButtonPressEvent window $ \button -> do
    btnNo <- GDK.getEventButtonButton button
    x     <- GDK.getEventButtonX button
    y     <- GDK.getEventButtonY button
    time  <- GDK.getEventButtonTime button
    case btnNo of
      1  -> do GTK.windowBeginMoveDrag window 1 (round x) (round y) time  -- left button
               return True
      2  -> do GTK.windowBeginResizeDrag window GDK.WindowEdgeSouthEast 2 -- middle button
                                         (round x) (round y) time
               return True
      _  -> return False

-}

  controller <- new Gtk.EventControllerKey [On #keyPressed myhandle]
  #addController window controller

  --------
  -- get my surface
  -- gdkwindow <- (castTo GDK.Window window)
  --
  -- on this surface I want to do my drawing operations, and then only "copy"
  -- them to the given surface in `onDraw`.
  -- Here I can do my custom computation of delta difference incurred by an input.
  --
  -- Since we create the surface using `createSimilarSurface`, it should be faster.
  -- See https://news.ycombinator.com/item?id=16539446
  --
  -- gdkwindow <- GTK.widgetGetWindow canvas
  -- case gdkwindow of
  --   Nothing -> error ""
  --   Just gdkwindow -> do
  --     mygoodsurface <- GDK.windowCreateSimilarSurface gdkwindow GI.Cairo.ContentColorAlpha 400 400
  --     renderWith (Surface mygoodsurface) undefined
  --     undefined
  --      -- mygoodsurface
  --     -- renderWith (Surface mygoodsurface) undefined
  --     return ()
  --
  --------


  GTK.setWindowDecorated window True
  GTK.setWindowResizable window True

  let renderer' = \widget ctx _ _ -> renderWithContext (renderer widget) ctx >> return ()

  GTK.drawingAreaSetDrawFunc canvas (Just renderer')

  -- we do not need a redraw queue
  -- timeoutAdd GI.GLib.PRIORITY_DEFAULT 1000 (GTK.widgetQueueDraw canvas >> return True)
  -- GTK.main

  #show window

main :: (forall widget. GTK.IsWidget widget => widget -> Render Bool)
     -> (Text -> IO ())
     -> IO ()
main renderer keyhandler = do
  -- app <- new Gtk.Application [#applicationId := "haskell-gi.Gtk4.test",
  --                             On #activate (activate ?self)]

  app <- new Gtk.Application [#applicationId := "haskell-gi.Gtk4.test"]
  set app [On #activate (activate renderer keyhandler app)]

  progName <- getProgName
  void $ #run app Nothing



{-
------------------------------------------------------------------
-- gtk4 example


-- | An example of a signal callback accessing the ?self parameter
-- (that is, the object raising the callback). See
-- https://github.com/haskell-gi/haskell-gi/issues/346
-- for why this is necessary when dealing with even controllers in gtk4.
pressedCB :: (?self :: Gtk.GestureClick) => Int32 -> Double -> Double -> IO ()
pressedCB nPress x y = do
    button <- #getCurrentButton ?self
    putStrLn $ "Button pressed: " <> show nPress <> " "
      <> show x <> " " <> show y <> " button: " <> show button

activate :: Gtk.Application -> IO ()
activate app = do
  box <- new Gtk.Box [#orientation := Gtk.OrientationVertical]

  adjustment <- new Gtk.Adjustment [#value := 50, #lower := 0, #upper := 100,
                                    #stepIncrement := 1]
  slider <- new Gtk.Scale[#adjustment := adjustment, #drawValue := True]
  #append box slider
  spinButton <- new Gtk.SpinButton [#adjustment := adjustment]
  #append box spinButton

  -- controller <- new Gtk.GestureClick [After #pressed pressedCB]
  controller <- new Gtk.GestureClick [] -- [After #pressed pressedCB]
  after controller #pressed (let ?self = controller in pressedCB)
  #addController slider controller

  window <- new Gtk.ApplicationWindow [#application := app,
                                       #title := "Hello",
                                       #child := box]
  #show window

main :: IO ()
main = do
  -- app <- new Gtk.Application [#applicationId := "haskell-gi.Gtk4.test",
  --                             On #activate (activate ?self)]

  app <- new Gtk.Application [#applicationId := "haskell-gi.Gtk4.test"]
  set app [On #activate (activate app)]
                              -- On #activate (activate ?self)]

  -- If the application does not need to parse command line arguments
  -- just pass Nothing.
  -- args <- Nothing -- getArgs
  progName <- getProgName
  void $ #run app Nothing -- (Just $ progName : args)
-}

