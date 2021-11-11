-- {-# OPTIONS --overlapping-instances #-}

module Verification.Core.Algebra.Ring.PartiallyOrdered where

open import Verification.Conventions

open import Verification.Core.Algebra.Setoid.Definition
open import Verification.Core.Algebra.Monoid.Definition
open import Verification.Core.Algebra.Group.Definition
open import Verification.Core.Algebra.Group.Quotient
open import Verification.Core.Algebra.Abelian.Definition
open import Verification.Core.Algebra.Ring.Definition
open import Verification.Core.Algebra.Ring.Domain
open import Verification.Core.Order.Preorder
open import Verification.Core.Order.Totalorder

module _ {𝑖 : 𝔏 ^ 2} where
  record isOrderedRing (𝑗 : 𝔏) (R : Ring 𝑖)  : 𝒰 (𝑖 ⁺ ､ 𝑗 ⁺) where
    field overlap {{OProof}} : ((isPreorder 𝑗 :> isPartialorder)) ′ ⟨ R ⟩ ′
    field cong-⋆-≤-r : ∀{a b c : ⟨ R ⟩} -> a ≤ b -> a ⋆ c ≤ b ⋆ c
          _⋅-isNonNegative_ : ∀{a b : ⟨ R ⟩} -> ◌ ≤ a -> ◌ ≤ b -> ◌ ≤ a ⋅ b

  open isOrderedRing {{...}} public


module _ {𝑖 : 𝔏 ^ 2} {𝑗 : 𝔏} where
  module _ {R : 𝒰 _} {_ : Ring 𝑖 on R} {{_ : isOrderedRing 𝑗 ′ R ′}} where

    ta : isRing ′ R ′
    ta = it
  -- module _ {R : Ring 𝑖} {{_ : isOrderedRing 𝑗 ′ ⟨ R ⟩ ′}} where
    cong-⋅-≤-r : ∀{a b c : R} -> a ≤ b -> (◌ ≤ c) -> a ⋅ c ≤ b ⋅ c
    cong-⋅-≤-r {a} {b} {c} p q =
      let P₀ = ◌       ⟨ inv-r-⋆ ⁻¹ ⟩-∼-≤
              a ⋆ ◡ a  ⟨ cong-⋆-≤-r p ⟩-≤
              b ⋆ ◡ a  ∎-≤

          P₁ = ◌                ⟨ P₀ ⋅-isNonNegative q ⟩-≤-∼
               (b ⋆ ◡ a) ⋅ c    ⟨ distr-r-⋅ ⟩-∼
               b ⋅ c ⋆ ◡ a ⋅ c  ∎-∼

          P₂ = a ⋅ c                      ⟨ unit-l-⋆ ⁻¹ ⟩-∼-≤
               ◌ ⋆ a ⋅ c                  ⟨ cong-⋆-≤-r P₁ ⟩-≤-∼
               (b ⋅ c ⋆ ◡ a ⋅ c) ⋆ a ⋅ c   ⟨ assoc-l-⋆ ⟩-∼
               b ⋅ c ⋆ (◡ a ⋅ c ⋆ a ⋅ c)   ⟨ refl ≀⋆≀ (switch-◡-⋅-l ⁻¹ ≀⋆≀ refl) ⟩-∼
               b ⋅ c ⋆ (◡(a ⋅ c) ⋆ a ⋅ c)  ⟨ refl ≀⋆≀ inv-l-⋆ ⟩-∼
               b ⋅ c ⋆ ◌                  ⟨ unit-r-⋆ ⟩-∼
               b ⋅ c                      ∎
      in P₂



  isPositive : {R : 𝒰 _} {{_ : Ring 𝑖 on R}} {{_ : isOrderedRing 𝑗 ′ R ′}} -> R -> 𝒰 _
  isPositive a = ◌ < a

  isNonNegative : {R : 𝒰 _} {{_ : Ring 𝑖 on R}} {{_ : isOrderedRing 𝑗 ′ R ′}} -> R -> 𝒰 _
  isNonNegative a = ◌ ≤ a

  record isDecidable-OrderedRing (R : Ring 𝑖 :& isOrderedRing 𝑗) : 𝒰 (𝑖 ⁺ ､ 𝑗 ⁺) where
    field overlap {{DecOProof}} : (isTotalorder :> isDecidable-Totalorder) ′ ⟨ R ⟩ ′

  module _ (R : Ring 𝑖)
           {{_ : isDomain R}}
           {{_ : isOrderedRing 𝑗 R}} where
           -- {{_ : isDecidable-OrderedRing ′ ⟨ R ⟩ ′}} where

    cong-⋅-≤-r

    -- cancel-⋅-≤-r : ∀{a b c : ⟨ R ⟩} -> a ⋅ c ≤ b ⋅ c -> isPositive c -> a ≤ b
    -- cancel-⋅-≤-r =
    --   let P₀ : 









{-
  record isDecidable-OrderedRing (R : Ring 𝑖 :& isOrderedRing 𝑗) : 𝒰 (𝑖 ⁺ ､ 𝑗 ⁺) where
    field overlap {{DecOProof}} : (isTotalorder :> isDecidable-Totalorder) ′ ⟨ R ⟩ ′

-- module _ {𝑖 : 𝔏 ^ 2} {𝑗 : \}
  module _ (R : Ring 𝑖) {{_ : isOrderedRing 𝑗 R}} {{_ : isDecidable-OrderedRing ′ ⟨ R ⟩ ′}} where

    -- isPositive-⨡ : isPositive ⨡
    -- isPositive-⨡ with compare ◌ ⨡
    -- ... | LT x = {!!}
    -- ... | EQ x = transp-≤ {!!} {!!} refl-≤
    -- ... | GT x = {!!}

-}





