
module Hata.Runtime.Application.Render.Definition where

import Data.Text as Text

data StateCmd n x where
  ClearAll :: StateCmd n x
  Clear :: n -> StateCmd n x
  Set :: n -> x -> StateCmd n x


type Rat = (Integer,Integer)

type Location = (Rat,Rat)
type Extent = (Rat,Rat)

data RGB = RGB Integer Integer Integer

data BaseItem where
  StringBI :: RGB -> Integer -> Text  -> BaseItem
  RectangleBI :: RGB -> Extent -> BaseItem

data Item where
  Item :: Location -> BaseItem -> Item

data Cmd where
  DoRender :: ((Text -> Either () Extent) -> Extent -> [Item]) -> Cmd
  DoChangeState :: StateCmd Text BaseItem -> Cmd


fromRationalCoord :: Location -> (Double,Double)
fromRationalCoord (a,b)= (f a, f b)
  where
    f (x,dx) = fromIntegral x / fromIntegral dx

toRationalCoord :: (Double,Double) -> Location
toRationalCoord (a,b) = ((floor a,1), (floor b,1))

