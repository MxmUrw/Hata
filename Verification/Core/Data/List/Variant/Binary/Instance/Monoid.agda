
module Verification.Core.Data.List.Variant.Binary.Instance.Monoid where

open import Verification.Core.Conventions hiding (ℕ)

open import Verification.Core.Set.Decidable
open import Verification.Core.Set.Setoid.Definition
open import Verification.Core.Set.Setoid.Free
open import Verification.Core.Algebra.Monoid.Definition

open import Verification.Core.Data.List.Variant.Binary.Definition
open import Verification.Core.Data.List.Variant.Binary.Instance.Setoid




-- [Hide]
module _ {A : 𝒰 𝑖} where
  private
    lem-1 : ∀{a c d : ⋆List A} ->  (q : RST _∼-⋆List_ c d) -> RST _∼-⋆List_ (a ⋆-⧜ c) (a ⋆-⧜ d)
    lem-1 (incl x) = incl (cong-r-⋆-⧜ x)
    lem-1 refl-RST = refl-RST
    lem-1 (sym-RST q) = sym-RST (lem-1 q)
    lem-1 (p ∙-RST q) = lem-1 p ∙-RST lem-1 q

  cong-⋆-⧜ : ∀{a b c d : ⋆List A} -> (p : RST _∼-⋆List_ a b) (q : RST _∼-⋆List_ c d) -> RST _∼-⋆List_ (a ⋆-⧜ c) (b ⋆-⧜ d)
  cong-⋆-⧜ (incl x) q     = incl (cong-l-⋆-⧜ x) ∙-RST lem-1 q
  cong-⋆-⧜ refl-RST q     = lem-1 q
  cong-⋆-⧜ (sym-RST p) q  = sym-RST (cong-⋆-⧜ p (sym-RST q))
  cong-⋆-⧜ (p ∙-RST p') q = cong-⋆-⧜ p q ∙-RST cong-⋆-⧜ p' refl-RST
-- //


-- [Lemma]
-- | Let [..] be a type.
module _ {A : 𝒰 𝑖} where
  -- |> Then |⋆List A| is a monoid.
  instance
    isMonoid:⋆List : isMonoid (𝖥𝗋𝖾𝖾-𝐌𝐨𝐧 A)
    isMonoid:⋆List = record
      { _⋆_        = _⋆-⧜_
      ; ◌          = ◌-⧜
      ; unit-l-⋆   = incl unit-l-⋆-⧜
      ; unit-r-⋆   = incl unit-r-⋆-⧜
      ; assoc-l-⋆  = incl assoc-l-⋆-⧜
      ; _≀⋆≀_      = cong-⋆-⧜
      }

-- //

