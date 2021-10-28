
module Hata.Runtime.EventLoop where

import Hata.Runtime.Application
import Hata.Runtime.UI.Window
-- import Hata.Runtime.UI.Test as Test
import Hata.Runtime.UI.EditorMain as EditorMain
import Hata.Runtime.Application.Render.Definition

import Data.Text as T
import Data.IORef
import Data.HashMap.Strict as H

-- el_singleRun :: RegisterExecutable -> [Event] -> IO ()
-- el_singleRun (RegisterExecutable _ exec) events = el_steps exec events (initExec exec) >> pure ()

-- el_steps :: Executable a -> [Event] -> a -> IO a
-- el_steps x [] a = pure a
-- el_steps x (e : es) a = do
--   a' <- el_step x e a
--   el_steps x es a'

-- el_step :: Executable a -> Event -> a -> IO (a)
-- el_step x ev state = do
--   let (reactions,state') = (stepExec x ev state)
--   mapM react reactions
--   return state'

el_singleRun :: RegisterExecutable -> [Event] -> IO ()
el_singleRun (RegisterExecutable _ exec) events = do
  ref <- newIORef (initExec exec)
  el_steps exec events ref >> pure ()

el_steps :: Executable a -> [Event] -> IORef a -> IO ()
el_steps x [] a = pure ()
el_steps x (e : es) a = el_step x e a >> el_steps x es a

el_step :: Executable a -> Event -> IORef a -> IO ()
el_step x ev ref = do
  state <- readIORef ref
  let (reactions,state') = (stepExec x ev state)
  mapM (react x ref) reactions
  writeIORef ref state'


react :: Executable a -> IORef a -> Reaction a -> IO ()
react exe ref (Reaction_NewWindow cmd) = do
  drawStateRef <- newIORef (H.empty @Text @Extent)
  EditorMain.main
    (\a -> EditorMain.drawCommands a drawStateRef ref cmd)
    (\key -> el_step exe (Event_KeyPress key) ref)
react exe ref (Reaction_PrintDebug t) = putStrLn (T.unpack t)
react exe ref (Reaction_Exit) = undefined



