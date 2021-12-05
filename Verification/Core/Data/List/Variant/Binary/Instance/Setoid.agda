
module Verification.Core.Data.List.Variant.Binary.Instance.Setoid where

open import Verification.Core.Conventions


open import Verification.Core.Set.Decidable
open import Verification.Core.Set.Setoid.Definition
open import Verification.Core.Set.Setoid.Free

open import Verification.Core.Data.List.Variant.Binary.Definition


module _ {A : 𝒰 𝑖} where

  -- the setoid and monoid structure

  infix 10 _∼-⋆List_
  data _∼-⋆List_ : (a b : ⋆List A) -> 𝒰 𝑖 where
    unit-l-⋆-⧜  : ∀{a} -> ◌-⧜ ⋆-⧜ a ∼-⋆List a
    unit-r-⋆-⧜  : ∀{a} -> a ⋆-⧜ ◌-⧜ ∼-⋆List a
    assoc-l-⋆-⧜ : ∀{a b c} -> (a ⋆-⧜ b) ⋆-⧜ c ∼-⋆List a ⋆-⧜ (b ⋆-⧜ c)
    cong-l-⋆-⧜  : ∀{a b c} -> (a ∼-⋆List b) -> (a ⋆-⧜ c ∼-⋆List b ⋆-⧜ c)
    cong-r-⋆-⧜  : ∀{a b c} -> (b ∼-⋆List c) -> (a ⋆-⧜ b ∼-⋆List a ⋆-⧜ c)

  instance
    isSetoid:⋆List : isSetoid (⋆List A)
    isSetoid:⋆List = isSetoid:byFree _∼-⋆List_





  private
    lem-1 : ∀{a c d} ->  (q : RST _∼-⋆List_ c d) -> RST _∼-⋆List_ (a ⋆-⧜ c) (a ⋆-⧜ d)
    lem-1 (incl x) = incl (cong-r-⋆-⧜ x)
    lem-1 refl-RST = refl-RST
    lem-1 (sym-RST q) = sym-RST (lem-1 q)
    lem-1 (p ∙-RST q) = lem-1 p ∙-RST lem-1 q

  cong-⋆-⧜ : ∀{a b c d} -> (p : RST _∼-⋆List_ a b) (q : RST _∼-⋆List_ c d) -> RST _∼-⋆List_ (a ⋆-⧜ c) (b ⋆-⧜ d)
  cong-⋆-⧜ (incl x) q     = incl (cong-l-⋆-⧜ x) ∙-RST lem-1 q
  cong-⋆-⧜ refl-RST q     = lem-1 q
  cong-⋆-⧜ (sym-RST p) q  = sym-RST (cong-⋆-⧜ p (sym-RST q))
  cong-⋆-⧜ (p ∙-RST p') q = cong-⋆-⧜ p q ∙-RST cong-⋆-⧜ p' refl-RST


