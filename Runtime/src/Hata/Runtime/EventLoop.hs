
module Hata.Runtime.EventLoop where

import Hata.Runtime.Application
import Hata.Runtime.UI.Window

import Data.Text as T

el_singleRun :: RegisterExecutable -> [Event] -> IO ()
el_singleRun (RegisterExecutable _ exec) events = el_steps exec events (initExec exec) >> pure ()

el_steps :: Executable a -> [Event] -> a -> IO a
el_steps x [] a = pure a
el_steps x (e : es) a = do
  a' <- el_step x e a
  el_steps x es a'

el_step :: Executable a -> Event -> a -> IO (a)
el_step x ev state = do
  let (reactions,state') = (stepExec x ev state)
  mapM react reactions
  return state'

react :: Reaction -> IO ()
react Reaction_NewWindow = createWindow
react (Reaction_PrintDebug t) = putStrLn (T.unpack t)
react (Reaction_Exit) = undefined




