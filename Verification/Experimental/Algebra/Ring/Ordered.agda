
module Verification.Experimental.Algebra.Ring.Ordered where

open import Verification.Conventions
open import Verification.Experimental.Meta.Structure
open import Verification.Experimental.Set.Setoid.Definition
open import Verification.Experimental.Algebra.Monoid.Definition
open import Verification.Experimental.Algebra.Group.Definition
open import Verification.Experimental.Algebra.Group.Quotient
open import Verification.Experimental.Algebra.Abelian.Definition
open import Verification.Experimental.Algebra.Ring.Definition
open import Verification.Experimental.Algebra.Ring.Domain
open import Verification.Experimental.Order.Linearorder

module _ {𝑖 : 𝔏 ^ 2} where
  record isOrderedRing (𝑗 : 𝔏) (R : Ring 𝑖)  : 𝒰 (𝑖 ⁺ ､ 𝑗 ⁺) where
    field overlap {{OProof}} : isLinearorder 𝑗 ′ ⟨ R ⟩ ′
    field cong-⋆-<-r : ∀{a b c : ⟨ R ⟩} -> a < b -> a ⋆ c < b ⋆ c
          _⋅-isPositive_ : ∀{a b : ⟨ R ⟩} -> ◌ < a -> ◌ < b -> ◌ < a ⋅ b

  open isOrderedRing {{...}} public


module _ {𝑖 : 𝔏 ^ 2} {𝑗 : 𝔏} where
  module _ {R : 𝒰 _} {_ : Ring 𝑖 on R} {{_ : isOrderedRing 𝑗 ′ R ′}} where

    ta : isRing ′ R ′
    ta = it
  -- module _ {R : Ring 𝑖} {{_ : isOrderedRing 𝑗 ′ ⟨ R ⟩ ′}} where
    cong-⋅-<-r : ∀{a b c : R} -> a < b -> (◌ < c) -> a ⋅ c < b ⋅ c
    cong-⋅-<-r {a} {b} {c} p q =
      let P₀ = ◌       ⟨ inv-r-⋆ ⁻¹ ⟩-∼-<
              a ⋆ ◡ a  ⟨ cong-⋆-<-r p ⟩-<-∼
              b ⋆ ◡ a  ∎-∼

          P₁ = ◌                ⟨ P₀ ⋅-isPositive q ⟩-<-∼
               (b ⋆ ◡ a) ⋅ c    ⟨ distr-r-⋅ ⟩-∼
               b ⋅ c ⋆ ◡ a ⋅ c  ∎-∼

          P₂ = a ⋅ c                      ⟨ unit-l-⋆ ⁻¹ ⟩-∼-<
               ◌ ⋆ a ⋅ c                  ⟨ cong-⋆-<-r P₁ ⟩-<-∼
               (b ⋅ c ⋆ ◡ a ⋅ c) ⋆ a ⋅ c   ⟨ assoc-l-⋆ ⟩-∼
               b ⋅ c ⋆ (◡ a ⋅ c ⋆ a ⋅ c)   ⟨ refl ≀⋆≀ (switch-◡-⋅-l ⁻¹ ≀⋆≀ refl) ⟩-∼
               b ⋅ c ⋆ (◡(a ⋅ c) ⋆ a ⋅ c)  ⟨ refl ≀⋆≀ inv-l-⋆ ⟩-∼
               b ⋅ c ⋆ ◌                  ⟨ unit-r-⋆ ⟩-∼
               b ⋅ c                      ∎
      in P₂



  isPositive : {R : 𝒰 _} {{_ : Ring 𝑖 on R}} {{_ : isOrderedRing 𝑗 ′ R ′}} -> R -> 𝒰 _
  isPositive a = ◌ < a

  -- isNonNegative : {R : 𝒰 _} {{_ : Ring 𝑖 on R}} {{_ : isOrderedRing 𝑗 ′ R ′}} -> R -> 𝒰 _
  -- isNonNegative a = ◌ < a

  -- record isDecidable-OrderedRing (R : Ring 𝑖 :& isOrderedRing 𝑗) : 𝒰 (𝑖 ⁺ ､ 𝑗 ⁺) where
  --   field overlap {{DecOProof}} : (isTotalorder :> isDecidable-Totalorder) ′ ⟨ R ⟩ ′

  module _ {R : Ring 𝑖}
           -- {{_ : isDomain R}}
           {{_ : isOrderedRing 𝑗 R}} where
           -- {{_ : isDecidable-OrderedRing ′ ⟨ R ⟩ ′}} where

    -- cong-⋅-<-r

    cancel-⋅-<-r : ∀{a b c : ⟨ R ⟩} -> a ⋅ c < b ⋅ c -> isPositive c -> a < b
    cancel-⋅-<-r = {!!}

    -- module _ {R : Ring 𝑖}
    --         -- {{_ : isDomain R}}
    --         {{_ : isOrderedRing 𝑗 R}} where
    --   instance


    -- NOTE: We do not make this an instance, since not every domain structures comes from an ordered ring structure.
    isDomain:OrderedRing : isDomain R
    isDomain.domain isDomain:OrderedRing = {!!}



{-








{-
  record isDecidable-OrderedRing (R : Ring 𝑖 :& isOrderedRing 𝑗) : 𝒰 (𝑖 ⁺ ､ 𝑗 ⁺) where
    field overlap {{DecOProof}} : (isTotalorder :> isDecidable-Totalorder) ′ ⟨ R ⟩ ′

-- module _ {𝑖 : 𝔏 ^ 2} {𝑗 : \}
  module _ (R : Ring 𝑖) {{_ : isOrderedRing 𝑗 R}} {{_ : isDecidable-OrderedRing ′ ⟨ R ⟩ ′}} where

    -- isPositive-⨡ : isPositive ⨡
    -- isPositive-⨡ with compare ◌ ⨡
    -- ... | LT x = {!!}
    -- ... | EQ x = transp-< {!!} {!!} refl-<
    -- ... | GT x = {!!}

-}
-}



