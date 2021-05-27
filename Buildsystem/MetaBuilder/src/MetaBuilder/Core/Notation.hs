
module MetaBuilder.Core.Notation where

(.>) :: a -> (a -> b) -> b
(.>) x f = f x
infixl 9 .>

