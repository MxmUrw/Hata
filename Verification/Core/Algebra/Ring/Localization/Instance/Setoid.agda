
module Verification.Core.Algebra.Ring.Localization.Instance.Setoid where

open import Verification.Conventions

open import Verification.Core.Data.Prop.Everything
open import Verification.Core.Set.Setoid.Definition
open import Verification.Core.Algebra.Monoid.Definition
open import Verification.Core.Algebra.Group.Definition
-- open import Verification.Core.Algebra.Group.Quotient
open import Verification.Core.Algebra.Abelian.Definition
open import Verification.Core.Algebra.Ring.Definition
open import Verification.Core.Algebra.Ring.Localization.Definition



module _ {𝑖 : 𝔏 ^ 2} {R : CRing 𝑖} {M : MCS R} where
  LocRel : Localize R M -> Localize R M -> 𝒰 _
  LocRel (a / da) (b / db) = ∑ λ (t : ⦋ ⟨ M ⟩ ⦌) -> (a ⋅ ⟨ db ⟩ ⋅ ⟨ t ⟩) ∼ (b ⋅ ⟨ da ⟩ ⋅ ⟨ t ⟩)

  -- instance
  --   isEquivRel:LocRel : isEquivRel (∼-Base LocRel)
  --   isEquivRel.refl isEquivRel:LocRel {x = a / da} = incl ((⨡ ∢ closed-⨡) , refl)
  --   isEquivRel.sym isEquivRel:LocRel {x = a / da} {y = b / db} (incl (t , p)) = incl (t , sym p)
  --   isEquivRel._∙_ isEquivRel:LocRel {x = a / (da ∢ _)} {y = b / (db ∢ dbP)} {z = c / (dc ∢ _)} (incl ((s ∢ sP) , p)) (incl ((t ∢ tP) , q)) =
  --     let u : ⦋ ⟨ M ⟩ ⦌
  --         u = db ⋅ s ⋅ t ∢ closed-⋅ (closed-⋅ dbP sP) tP

  --         P : a ⋅ dc ⋅ ⟨ u ⟩ ∼ c ⋅ da ⋅ ⟨ u ⟩
  --         P = a ⋅ dc ⋅ (db ⋅ s ⋅ t)     ≣⟨ assoc-l-⋅ ⟩
  --             a ⋅ (dc ⋅ (db ⋅ s ⋅ t))   ≣⟨ refl `cong-⋅` comm-⋅ ⟩
  --             a ⋅ ((db ⋅ s ⋅ t) ⋅ dc)   ≣⟨ assoc-r-⋅ ⟩
  --             a ⋅ (db ⋅ s ⋅ t) ⋅ dc     ≣⟨ assoc-r-⋅ `cong-⋅` refl ⟩
  --             a ⋅ (db ⋅ s) ⋅ t ⋅ dc     ≣⟨ (assoc-r-⋅ ∙ p ∙ assoc-l-⋅) `cong-⋅` refl `cong-⋅` refl ⟩
  --             b ⋅ (da ⋅ s) ⋅ t ⋅ dc     ≣⟨ comm-⋅ `cong-⋅` refl `cong-⋅` refl ⟩
  --             (da ⋅ s) ⋅ b ⋅ t ⋅ dc     ≣⟨ assoc-l-⋅ `cong-⋅` refl ⟩
  --             (da ⋅ s) ⋅ (b ⋅ t) ⋅ dc   ≣⟨ assoc-l-⋅ ⟩
  --             (da ⋅ s) ⋅ (b ⋅ t ⋅ dc)   ≣⟨ refl `cong-⋅` assoc-l-⋅ ⟩
  --             (da ⋅ s) ⋅ (b ⋅ (t ⋅ dc)) ≣⟨ refl `cong-⋅` (refl `cong-⋅` comm-⋅) ⟩
  --             (da ⋅ s) ⋅ (b ⋅ (dc ⋅ t)) ≣⟨ refl `cong-⋅` (assoc-r-⋅ ∙ q) ⟩
  --             (da ⋅ s) ⋅ (c ⋅ db ⋅ t)   ≣⟨ assoc-l-⋅ ⟩
  --             da ⋅ (s ⋅ (c ⋅ db ⋅ t))   ≣⟨ refl `cong-⋅` comm-⋅ ⟩
  --             da ⋅ (c ⋅ db ⋅ t ⋅ s)     ≣⟨ refl `cong-⋅` assoc-l-⋅ ⟩
  --             da ⋅ (c ⋅ db ⋅ (t ⋅ s))   ≣⟨ refl `cong-⋅` assoc-l-⋅ ⟩
  --             da ⋅ (c ⋅ (db ⋅ (t ⋅ s))) ≣⟨ assoc-r-⋅ ⟩
  --             (da ⋅ c) ⋅ (db ⋅ (t ⋅ s)) ≣⟨ comm-⋅ `cong-⋅` ((refl `cong-⋅` comm-⋅) ∙ assoc-r-⋅) ⟩
  --             c ⋅ da ⋅ (db ⋅ s ⋅ t)     ∎
  --     in incl (u , P)

  instance
    isSetoid:Localize : isSetoid (Localize R M)
    isSetoid._∼_ isSetoid:Localize = ∼-Base LocRel
    isSetoid.refl isSetoid:Localize {a = a / da} = incl ((⨡ ∢ closed-⨡) , refl)
    isSetoid.sym isSetoid:Localize {a = a / da} {b = b / db} (incl (t , p)) = incl (t , sym p)
    isSetoid._∙_ isSetoid:Localize {a = a / (da ∢ _)} {b = b / (db ∢ dbP)} {c = c / (dc ∢ _)} (incl ((s ∢ sP) , p)) (incl ((t ∢ tP) , q)) =
      let u : ⦋ ⟨ M ⟩ ⦌
          u = db ⋅ s ⋅ t ∢ closed-⋅ (closed-⋅ dbP sP) tP

          P : a ⋅ dc ⋅ ⟨ u ⟩ ∼ c ⋅ da ⋅ ⟨ u ⟩
          P = a ⋅ dc ⋅ (db ⋅ s ⋅ t)     ≣⟨ assoc-l-⋅ ⟩
              a ⋅ (dc ⋅ (db ⋅ s ⋅ t))   ≣⟨ refl `cong-⋅` comm-⋅ ⟩
              a ⋅ ((db ⋅ s ⋅ t) ⋅ dc)   ≣⟨ assoc-r-⋅ ⟩
              a ⋅ (db ⋅ s ⋅ t) ⋅ dc     ≣⟨ assoc-r-⋅ `cong-⋅` refl ⟩
              a ⋅ (db ⋅ s) ⋅ t ⋅ dc     ≣⟨ (assoc-r-⋅ ∙ p ∙ assoc-l-⋅) `cong-⋅` refl `cong-⋅` refl ⟩
              b ⋅ (da ⋅ s) ⋅ t ⋅ dc     ≣⟨ comm-⋅ `cong-⋅` refl `cong-⋅` refl ⟩
              (da ⋅ s) ⋅ b ⋅ t ⋅ dc     ≣⟨ assoc-l-⋅ `cong-⋅` refl ⟩
              (da ⋅ s) ⋅ (b ⋅ t) ⋅ dc   ≣⟨ assoc-l-⋅ ⟩
              (da ⋅ s) ⋅ (b ⋅ t ⋅ dc)   ≣⟨ refl `cong-⋅` assoc-l-⋅ ⟩
              (da ⋅ s) ⋅ (b ⋅ (t ⋅ dc)) ≣⟨ refl `cong-⋅` (refl `cong-⋅` comm-⋅) ⟩
              (da ⋅ s) ⋅ (b ⋅ (dc ⋅ t)) ≣⟨ refl `cong-⋅` (assoc-r-⋅ ∙ q) ⟩
              (da ⋅ s) ⋅ (c ⋅ db ⋅ t)   ≣⟨ assoc-l-⋅ ⟩
              da ⋅ (s ⋅ (c ⋅ db ⋅ t))   ≣⟨ refl `cong-⋅` comm-⋅ ⟩
              da ⋅ (c ⋅ db ⋅ t ⋅ s)     ≣⟨ refl `cong-⋅` assoc-l-⋅ ⟩
              da ⋅ (c ⋅ db ⋅ (t ⋅ s))   ≣⟨ refl `cong-⋅` assoc-l-⋅ ⟩
              da ⋅ (c ⋅ (db ⋅ (t ⋅ s))) ≣⟨ assoc-r-⋅ ⟩
              (da ⋅ c) ⋅ (db ⋅ (t ⋅ s)) ≣⟨ comm-⋅ `cong-⋅` ((refl `cong-⋅` comm-⋅) ∙ assoc-r-⋅) ⟩
              c ⋅ da ⋅ (db ⋅ s ⋅ t)     ∎
      in incl (u , P)




    -- isSetoid._∼'_ isSetoid:Localize = LocRel
    -- isSetoid.isEquivRel:∼ isSetoid:Localize = {!!}




