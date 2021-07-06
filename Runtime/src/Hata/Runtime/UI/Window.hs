
{-# LANGUAGE OverloadedStrings, OverloadedLabels #-}

module Hata.Runtime.UI.Window where


import qualified GI.Gtk as Gtk
import Data.GI.Base

createWindow :: IO ()
createWindow = do
  Gtk.init Nothing

  win <- new Gtk.Window [ #title := "Hi there" ]

  on win #destroy Gtk.mainQuit

  button <- new Gtk.Button [ #label := "Click me" ]

  on button #clicked (set button [ #sensitive := False,
                                   #label := "Thanks for clicking me" ])

  #add win button

  #showAll win

  Gtk.main



