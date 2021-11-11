
module Verification.Explorational.Homotopy.Cardinalities where

open import Verification.Conventions hiding (Path) public

_○_ = trans-Path

data Circle : 𝒰₀ where
  pt : Circle
  @0 loop : pt ≡ pt


data Circle' : 𝒰₀ where
  pta : Circle'
  ptb : Circle'
  @0 patha : pta ≡ ptb
  @0 pathb : pta ≡ ptb


f : Circle -> Circle'
f pt = pta
f (loop i) = {!!}





