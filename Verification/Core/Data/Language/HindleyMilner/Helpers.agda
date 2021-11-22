
module Verification.Core.Data.Language.HindleyMilner.Helpers where

open import Verification.Conventions hiding (lookup ; ℕ ; _⊔_)
open import Verification.Core.Set.Setoid.Definition
open import Verification.Core.Set.Discrete
open import Verification.Core.Algebra.Monoid.Definition
open import Verification.Core.Algebra.Monoid.Free
open import Verification.Core.Data.AllOf.Collection.Basics
open import Verification.Core.Data.AllOf.Collection.TermTools
open import Verification.Core.Category.Std.AllOf.Collection.Basics
open import Verification.Core.Category.Std.AllOf.Collection.Limits

open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Category.Std.Limit.Specific.Coequalizer
open import Verification.Core.Computation.Unification.Definition

open import Verification.Core.Theory.Std.Specific.ProductTheory.Module
open import Verification.Core.Theory.Std.Specific.ProductTheory.Instance.hasBoundaries




module _ {A : 𝒰 𝑖} {B : A -> 𝒰 𝑗} (C : ∀{a} -> B a -> 𝒰 𝑘) where
  data DDList : {as : List A} (bs : DList B as) -> 𝒰 (𝑖 ､ 𝑗 ､ 𝑘) where
    [] : DDList []
    _∷_ : ∀{a as} -> {b : B a} {bs : DList B as} -> (c : C b) -> (cs : DDList bs) -> DDList (b ∷ bs)




