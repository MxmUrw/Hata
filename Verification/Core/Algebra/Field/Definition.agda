
module Verification.Core.Algebra.Field.Definition where

open import Verification.Conventions

open import Verification.Core.Data.Prop.Everything
open import Verification.Core.Set.Setoid.Definition
open import Verification.Core.Algebra.Monoid.Definition
open import Verification.Core.Algebra.Group.Definition
open import Verification.Core.Algebra.Abelian.Definition
open import Verification.Core.Algebra.Ring.Definition


𝟭 = ⨡

module _ {A : 𝒰 _} {{_ : Monoid 𝑖 on A}} where
  record not-◌ (a : A) : 𝒰 𝑖 where
    constructor incl
    field ⟨_⟩ : a ≁ ◌

  open not-◌ public

record isField (R : Ring 𝑖) : 𝒰 𝑖 where
  field ⟌ : (a : ⟨ R ⟩) -> {{not-◌ a}} -> ⟨ R ⟩
  field inv-l-⋅ : ∀{a : ⟨ R ⟩} -> {{_ : not-◌ a}} -> ⟌ a ⋅ a ∼ 𝟭
  field inv-r-⋅ : ∀{a} -> {{_ : not-◌ a}} -> a ⋅ ⟌ a ∼ 𝟭
  field nontrivial-Field : ◌ ≁ 𝟭

open isField {{...}} public

Field : ∀ 𝑖 -> 𝒰 _
Field 𝑖 = Ring 𝑖 :& isField






