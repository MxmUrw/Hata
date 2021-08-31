
module Verification.Experimental.Theory.Std.Specific.ProductTheory.Definition where

open import Verification.Conventions hiding (_⊔_)

open import Verification.Experimental.Set.Discrete
open import Verification.Experimental.Algebra.Monoid.Definition
open import Verification.Experimental.Algebra.Monoid.Free
open import Verification.Experimental.Algebra.Monoid.Free.Element
-- open import Verification.Experimental.Order.Lattice
open import Verification.Experimental.Data.Universe.Everything
open import Verification.Experimental.Data.Product.Definition
-- open import Verification.Experimental.Theory.Std.Generic.TypeTheory.Definition
-- open import Verification.Experimental.Theory.Std.Generic.TypeTheory.Simple
-- open import Verification.Experimental.Theory.Std.Generic.TypeTheory.Simple.Judgement2
-- open import Verification.Experimental.Theory.Std.TypologicalTypeTheory.CwJ.Kinding
-- open import Verification.Experimental.Theory.Std.Generic.TypeTheory.Simple
-- open import Verification.Experimental.Theory.Std.Specific.MetaTermCalculus2.Pattern.Definition

open import Verification.Experimental.Category.Std.Category.Definition
open import Verification.Experimental.Category.Std.Category.Structured.Monoidal.Definition
open import Verification.Experimental.Category.Std.Functor.Definition
open import Verification.Experimental.Category.Std.RelativeMonad.Definition
open import Verification.Experimental.Category.Std.RelativeMonad.KleisliCategory.Definition
open import Verification.Experimental.Category.Std.Category.Subcategory.Definition
open import Verification.Experimental.Category.Std.Morphism.EpiMono
-- open import Verification.Experimental.Category.Std.Limit.Specific.Coproduct.Preservation.Definition
open import Verification.Experimental.Category.Std.Limit.Specific.Coproduct.Definition

open import Verification.Experimental.Data.Nat.Free
open import Verification.Experimental.Data.Indexed.Definition
open import Verification.Experimental.Data.Indexed.Instance.Monoid
open import Verification.Experimental.Data.FiniteIndexed.Definition
open import Verification.Experimental.Data.Renaming.Definition
open import Verification.Experimental.Data.Renaming.Instance.CoproductMonoidal
open import Verification.Experimental.Data.Substitution.Definition

open import Verification.Experimental.Theory.Std.Generic.FormalSystem.Definition

-- record ProductTheoryType (s : 𝒰 𝑖) : 𝒰 𝑖 where
--   constructor _⇒_
--   field fst : List s
--   field snd : s
-- open ProductTheoryType public

record ProductTheory (𝑖 : 𝔏) : 𝒰 (𝑖 ⁺) where
  field Sort : 𝒰 𝑖
  field {{isDiscrete:Sort}} : isDiscrete Sort
  field {{isSet-Str:Sort}} : isSet-Str Sort
  field Con : List Sort -> Sort -> 𝒰 𝑖
  field {{isDiscrete:Con}} : ∀{αs α} -> isDiscrete (Con αs α)


open ProductTheory public

module _ (𝑖 : 𝔏) where
  macro 𝕋× = #structureOn (ProductTheory 𝑖)

Type-𝕋× : ProductTheory 𝑖 -> 𝒰 𝑖
Type-𝕋× a = Sort a

mutual
  data Terms-𝕋× (𝑨 : 𝕋× 𝑖) : (Γ : 𝐅𝐢𝐧𝐈𝐱 (Type-𝕋× 𝑨)) (Δ : 𝐅𝐢𝐧𝐈𝐱 (Type-𝕋× 𝑨)) -> 𝒰 𝑖 where
    -- incl : 𝑒𝑙 ⟨ Γ ⟩ ⟶ (Term-𝕋× 𝑨 Δ) -> Terms-𝕋× 𝑨 Γ Δ

    ◌-⧜ : ∀{Γ} -> Terms-𝕋× 𝑨 ⊥ Γ
    _⋆-⧜_ : ∀{Γ α β} -> Terms-𝕋× 𝑨 α Γ -> Terms-𝕋× 𝑨 β Γ -> Terms-𝕋× 𝑨 (α ⊔ β) Γ
    incl : ∀{Γ s} -> Term₁-𝕋× 𝑨 ⟨ Γ ⟩ s -> Terms-𝕋× 𝑨 (incl (incl s)) Γ


  data Term₁-𝕋× (a : 𝕋× 𝑖) : (Γ : 人List (Type-𝕋× a)) (τ : Type-𝕋× a) -> 𝒰 𝑖 where
    var : ∀{τ Γ} -> Γ ∍ τ -> Term₁-𝕋× a Γ τ
    con : ∀{Γ αs α} -> (c : Con a αs α) -> Terms-𝕋× a (incl (ι αs)) (incl Γ) -> Term₁-𝕋× a Γ α

  Term-𝕋× : (a : 𝕋× 𝑖) -> (𝐅𝐢𝐧𝐈𝐱 (Type-𝕋× a)) -> (𝐈𝐱 (Type-𝕋× a) (𝐔𝐧𝐢𝐯 𝑖))
  Term-𝕋× a Γ = indexed (λ τ → Term₁-𝕋× a ⟨ Γ ⟩ τ)




  -- freeVars-𝕋× : ∀{Γ τ} -> Term₁-𝕋× 𝑨 Γ τ -> 人List (Sort 𝑨)
  -- freeVars-𝕋× (var x) = incl x
  -- freeVars-𝕋× (con c x) = {!!}




  -- isFormalSystem.Type isFormalSystem:ProductTheory = ProductTheoryType
  -- isFormalSystem.Term isFormalSystem:ProductTheory = {!!}

