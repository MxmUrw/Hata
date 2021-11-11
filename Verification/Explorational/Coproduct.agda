
module Verification.Temporary.Coproduct where

open import Verification.Conventions
open import Verification.Core.Data.Sum.Definition
open import Verification.Core.Data.Universe.Definition
_+_ = _+-𝒰_
pattern ι₀ = left
pattern ι₁ = right
[_,_] = either
_◆_ = _◆-𝒰_
infixl 40 _◆_
id = id-𝒰

postulate
  B C D ξ : 𝒰₀
  h : B + ξ -> D
  π : B -> C + ξ
  i : C -> D + ξ
  P₀ : ∀ a -> (π ◆ [ i , ι₁ ]) a ≡ (ι₀ ◆ h ◆ ι₀) a

thm1 : π ◆ [ i ◆ [ id , ι₁ ◆ h ] , ι₁ ◆ h ] ≡ ι₀ ◆ h
thm1 = {!!}

thm2 : ∀ a -> (π ◆ [ i ◆ [ id , ι₁ ◆ h ] , ι₁ ◆ h ]) a ≡ (ι₀ ◆ h) a
thm2 a with split-+ (π a)
... | left (x , g) =
  let -- P₃ : (π ◆ i ◆ [ id , ι₁ ◆ h ]) (x) ≡ (π ◆ ι₀ ◆ h) a
      -- P₃ = ?

      P₂ : (i ◆ [ id , ι₁ ◆ h ]) (x) ≡ (ι₀ ◆ h) a
      P₂ = {!!}

      P₁ : ([ i ◆ [ id , ι₁ ◆ h ] , ι₁ ◆ h ]) (left x) ≡ (ι₀ ◆ h) a
      P₁ = P₂
  in {!!}
... | just (x , g) =
  let P₁ : [ i , ι₁ ] (just x) ≡ (ι₀ ◆ h ◆ ι₀) (a)
      P₁ = transport (λ j -> [ i , ι₁ ] (g j) ≡ (ι₀ ◆ h ◆ ι₀) a) (P₀ a)
  in 𝟘-rec (right≢left P₁)





