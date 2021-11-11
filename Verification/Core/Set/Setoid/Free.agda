
module Verification.Core.Set.Setoid.Free where

open import Verification.Core.Conventions
open import Verification.Core.Data.Prop.Definition
open import Verification.Core.Data.Product.Definition
open import Verification.Core.Set.Setoid.Definition



module _ {A : 𝒰 𝑖} (R : A -> A -> 𝒰 𝑗) where
  data RST : A -> A -> 𝒰 (𝑖 ､ 𝑗) where
    incl : ∀{a b} -> R a b -> RST a b
    refl-RST : ∀{a} -> RST a a
    sym-RST : ∀{a b} -> RST a b -> RST b a
    _∙-RST_ : ∀{a b c} -> RST a b -> RST b c -> RST a c


module _ {A : 𝒰 𝑖} {R : A -> A -> 𝒰 𝑗} {X : 𝒰 𝑘} {{_ : isSetoid {𝑙} X}} where
  rec-RST : {f : A -> X} (F : ∀{a b} -> R a b -> f a ∼ f b) -> ∀{a b} -> RST R a b -> f a ∼ f b
  rec-RST F (incl x) = F x
  rec-RST F refl-RST = refl
  rec-RST F (sym-RST p) = sym (rec-RST F p)
  rec-RST F (p ∙-RST q) = rec-RST F p ∙ rec-RST F q


-- record Free-𝐒𝐭𝐝 (A : 𝒰 𝑖) (E : A -> A -> 𝒰 𝑗) : 𝒰 𝑖 where


module _ {A : 𝒰 𝑖} where
  isSetoid:byFree : (R : A -> A -> 𝒰 𝑗) -> isSetoid A
  isSetoid:byFree R = setoid (RST R) refl-RST sym-RST _∙-RST_



