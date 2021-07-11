
module Verification.Experimental.Data.Product.Definition where

open import Verification.Conventions


macro
  _×_ : ∀{𝑖 𝑗 : 𝔏} {𝑘 𝑙 : 𝔏 ^ 2} -> (𝒰' 𝑖) [ 𝑙 ]→ (𝒰' 𝑗) [ 𝑘 ]→ SomeStructure
  _×_ = λstr A ↦ λstr B ↦ #structureOn (A ×-𝒰 B)
  infixr 40 _×_




-- The product for haskell


record _×~_ (A : 𝒰 𝑖) (B : 𝒰 𝑗) : 𝒰 (𝑖 ､ 𝑗) where
  constructor _,_
  field fst : A
  field snd : B


{-# FOREIGN GHC type AgdaProduct a b = (,) #-}
-- {-# FOREIGN GHC makeProduct a b = (a,b) #-}
{-# COMPILE GHC _×~_ = data AgdaProduct ((,)) #-}

