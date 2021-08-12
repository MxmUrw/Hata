
module Verification.Experimental.Data.Indexed.Instance.SeparatingFamily where

open import Verification.Conventions

open import Verification.Experimental.Set.Setoid.Definition
open import Verification.Experimental.Set.Decidable
open import Verification.Experimental.Category.Std.Category.Definition
open import Verification.Experimental.Category.Std.Morphism.Iso
open import Verification.Experimental.Category.Std.Functor.Definition
open import Verification.Experimental.Category.Std.Functor.Adjoint
open import Verification.Experimental.Data.Universe.Definition
open import Verification.Experimental.Data.Product.Definition
open import Verification.Experimental.Data.Sum.Definition
open import Verification.Experimental.Category.Std.Category.Structured.SeparatingFamily
open import Verification.Experimental.Category.Std.Limit.Specific.Coproduct.Definition
open import Verification.Experimental.Data.Universe.Instance.Category

open import Verification.Experimental.Data.Universe.Definition
open import Verification.Experimental.Data.Universe.Everything
open import Verification.Experimental.Data.Indexed.Definition
open import Verification.Experimental.Data.Indexed.Xiix




module _ {𝒞 : Category 𝑖} {{_ : hasSeparatingFamily 𝑘 𝒞}} {{_ : hasInitial 𝒞}}
         {I : 𝒰 𝑘} {{_ : isDiscrete I}}
         where

  Separator-𝐈𝐱 : 𝒰 _
  Separator-𝐈𝐱 = (Separator × I)

  Fam : (i j : I) -> 𝒰 𝑘
  Fam i j = i ≣ j

  separator-𝐈𝐱 : Separator-𝐈𝐱 -> 𝐈𝐱 I 𝒞
  separator-𝐈𝐱 (s , i) = 𝑥𝑖ₗ i (separator s)

  instance
    isSeparatingFamily:sep : isSeparatingFamily (𝐈𝐱 I 𝒞) separator-𝐈𝐱
    isSeparatingFamily.separate isSeparatingFamily:sep {a = a} {b} ϕ ψ p i = P
      where
        P : ϕ i ∼ ψ i
        P = separate (ϕ i) (ψ i) (λ ξ →
              let p' : free ξ ◆ ϕ ∼ free ξ ◆ ψ
                  p' = p (free ξ)

              in destruct-precomp-free p'
            )


  instance
    hasSeparatingFamily:𝐈𝐱 : hasSeparatingFamily 𝑘 (𝐈𝐱 I 𝒞)
    hasSeparatingFamily.Separator hasSeparatingFamily:𝐈𝐱 = Separator-𝐈𝐱
    hasSeparatingFamily.separator hasSeparatingFamily:𝐈𝐱 = separator-𝐈𝐱
    hasSeparatingFamily.isSeparatingFamily:seperators hasSeparatingFamily:𝐈𝐱 = it




