
{-# LANGUAGE OverloadedStrings, OverloadedLabels #-}

module Hata.Runtime.UI.Window where


import qualified GI.Gtk as Gtk
import Data.GI.Base

createWindow :: IO ()
createWindow = undefined {- do
  Gtk.init Nothing

  win <- new Gtk.Window [ #title := "Hi there" ]

  on win #destroy Gtk.mainQuit

  box <- new Gtk.Box []

  button <- new Gtk.Button [ #label := "Click me" ]
  button2 <- new Gtk.Button [ #label := "Click me too" ]

  on button #clicked (do set button [ #sensitive := False,
                                      #label := "Thanks for clicking me" ]
                         putStrLn "I got something??!")

  on button2 #released (putStrLn "Yes?")

  #add box button
  #add box button2

  #add win box

  #showAll win

  Gtk.main
-}


