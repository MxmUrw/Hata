
module Verification.Experimental.Algebra.Ring.Localization.Instance.Group where

open import Verification.Conventions
open import Verification.Experimental.Meta.Structure
open import Verification.Experimental.Set.Setoid.Definition
open import Verification.Experimental.Algebra.Monoid.Definition
open import Verification.Experimental.Algebra.Group.Definition
-- open import Verification.Experimental.Algebra.Group.Quotient
open import Verification.Experimental.Algebra.Abelian.Definition
open import Verification.Experimental.Algebra.Ring.Definition
open import Verification.Experimental.Algebra.Ring.Localization.Definition
open import Verification.Experimental.Algebra.Ring.Localization.Instance.Setoid
open import Verification.Experimental.Algebra.Ring.Localization.Instance.Monoid


module _ {𝑖 : 𝔏 ^ 2} {R : CRing 𝑖} {M : MCS R} where
  private
    ◡-Loc : Localize R M -> Localize R M
    ◡-Loc (a / da) = ◡ a / da

    lem-10 : ∀{a : Localize R M} -> ◡-Loc a ⋆ a ∼ ◌
    lem-10 {a / (da ∈ _)} =
      let P : (◡ a ⋅ da ⋆ a ⋅ da) ⋅ ⨡ ∼ ◌ ⋅ (da ⋅ da)
          P = (◡ a ⋅ da ⋆ a ⋅ da) ⋅ ⨡   ≣⟨ (switch-◡-⋅-l ⁻¹ ≀⋆≀ ─) ≀⋅≀ ─ ⟩
              (◡ (a ⋅ da) ⋆ a ⋅ da) ⋅ ⨡ ≣⟨ inv-l-⋆ ≀⋅≀ ─ ⟩
              ◌ ⋅ ⨡                    ≣⟨ reduce-⋅◌-l ⟩
              ◌                        ≣⟨ reduce-⋅◌-l ⁻¹ ⟩
              ◌ ⋅ (da ⋅ da)             ∎
      in incl (⨡-MCS , P ≀⋅≀ ─)

    lem-20 : ∀{a b : Localize R M} -> a ∼ b -> ◡-Loc a ∼ ◡-Loc b
    lem-20 {a / (da ∈ _)} {b / (db ∈ _)} (incl ((s ∈ sP) , p)) =
      let P : ◡ a ⋅ db ⋅ s ∼ ◡ b ⋅ da ⋅ s
          P = ◡ a ⋅ db ⋅ s       ≣⟨ switch-◡-⋅-l ⁻¹ ≀⋅≀ ─ ⟩
              ◡ (a ⋅ db) ⋅ s     ≣⟨ switch-◡-⋅-l ⁻¹ ⟩
              ◡ (a ⋅ db ⋅ s)     ≣⟨ ◡≀ p ⟩
              ◡ (b ⋅ da ⋅ s)     ≣⟨ switch-◡-⋅-l ⟩
              ◡ (b ⋅ da) ⋅ s     ≣⟨ switch-◡-⋅-l ≀⋅≀ ─ ⟩
              ◡ b ⋅ da ⋅ s       ∎
      in incl (s ∈ sP , P)

  instance
    isGroup:Localize : isGroup ′ Localize R M ′
    isGroup.◡_ isGroup:Localize a = ◡-Loc a
    isGroup.inv-l-⋆ isGroup:Localize = lem-10
    isGroup.inv-r-⋆ isGroup:Localize = comm-⋆ ∙ lem-10
    isGroup.cong-◡_ isGroup:Localize = lem-20



