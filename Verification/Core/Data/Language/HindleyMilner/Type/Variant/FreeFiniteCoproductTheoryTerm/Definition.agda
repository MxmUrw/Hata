
module Verification.Core.Data.Language.HindleyMilner.Type.Variant.FreeFiniteCoproductTheoryTerm.Definition where


open import Verification.Conventions hiding (ℕ ; _⊔_)
open import Verification.Core.Set.Setoid.Definition
open import Verification.Core.Set.Discrete
open import Verification.Core.Algebra.Monoid.Definition

open import Verification.Core.Data.Product.Definition

open import Verification.Core.Data.Nat.Free
open import Verification.Core.Data.Universe.Instance.Category
open import Verification.Core.Data.List.Variant.Unary.Definition
open import Verification.Core.Data.List.Variant.Unary.Element
open import Verification.Core.Data.List.Variant.Unary.Natural
open import Verification.Core.Data.List.Variant.Binary.Definition
open import Verification.Core.Data.List.Dependent.Variant.Unary.Definition
open import Verification.Core.Data.List.Dependent.Variant.Binary.Definition
open import Verification.Core.Data.Substitution.Variant.Base.Definition

-- open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Category.Std.Limit.Specific.Coequalizer
open import Verification.Core.Category.Std.Limit.Specific.Coproduct.Definition using (append-⦗⦘ ; ⦗≀_≀⦘)
open import Verification.Core.Category.Std.Limit.Specific.Coproduct.Instance.Functor
  -- renaming (_⇃⊔⇂_ to _⇃⊔⇂ᵘ_)

open import Verification.Core.Computation.Unification.Definition

open import Verification.Core.Theory.Std.Specific.FreeFiniteCoproductTheory.Param
open import Verification.Core.Theory.Std.Specific.FreeFiniteCoproductTheory.Definition
open import Verification.Core.Theory.Std.Specific.FreeFiniteCoproductTheory.Instance.Functor
open import Verification.Core.Theory.Std.Specific.FreeFiniteCoproductTheory.Instance.RelativeMonad
open import Verification.Core.Theory.Std.Specific.FreeFiniteCoproductTheory.Unification

open import Verification.Core.Data.Language.HindleyMilner.Helpers
open import Verification.Core.Data.Language.HindleyMilner.Type.Variant.FreeFiniteCoproductTheoryTerm.Signature

--------------------------------------
-- optimizations

open Overwrite:isCategory:⧜𝒯⊔Term 𝒹
open Overwrite:isCoproduct:⧜𝒯⊔Term 𝒹
open Overwrite:hasCoproducts:⧜𝒯⊔Term 𝒹
open Overwrite:hasFiniteCoproducts:⧜𝒯⊔Term 𝒹
open Overwrite:hasInitial:⧜𝒯⊔Term 𝒹
open Overwrite:isInitial:⧜𝒯⊔Term 𝒹

private
  _⟶_ = Hom
  -- _≅_ = _≅ᵘ_ {𝒞 = ⧜𝒯⊔Term 𝒹} {{isCategory:⧜𝐒𝐮𝐛𝐬𝐭 {T = 𝒯⊔term 𝒹}}}
  -- ⟨_⟩⁻¹ = ⟨_⟩⁻¹ᵘ {𝒞 = ⧜𝒯⊔Term 𝒹} {{isCategory:⧜𝐒𝐮𝐛𝐬𝐭 {T = 𝒯⊔term 𝒹}}}


-- abstract
--   infixl 100 _⇃⊔⇂_
--   _⇃⊔⇂_ : ∀{a b c d : ⧜𝒯⊔Term 𝒹} -> (a ⟶ b) -> (c ⟶ d) -> (a ⊔ c ⟶ b ⊔ d)
--   _⇃⊔⇂_ = _⇃⊔⇂ᵘ_



--------------------------------------
-- actual beginning

-- [Notation]
-- | We write |ℒHMType| for a term in that signature, i.e.:
ℒHMType : (Γ : 人ℕ) -> 𝒰₀
ℒHMType Γ = 𝒯⊔Term 𝒹 Γ tt
-- //

-- [Notation]
-- | We denote the category of type substitutions by:
ℒHMTypesᵘ : 𝒰₀
ℒHMTypesᵘ = ⧜𝐒𝐮𝐛𝐬𝐭 (𝒯⊔term 𝒹)

macro ℒHMTypes = #structureOn ℒHMTypesᵘ

-- //

-- [Hide]
st : ℒHMTypes
st = incl (incl tt)


asArr : ∀ {a} -> ℒHMType ⟨ a ⟩ -> st ⟶ a
asArr t = ⧜subst (incl t)

fromArr : ∀ {a} -> st ⟶ a -> ℒHMType ⟨ a ⟩
fromArr (⧜subst (incl x)) = x

abstract
  unify-ℒHMTypes : ∀{a b : ℒHMTypes} -> (f g : a ⟶ b) -> (¬ hasCoequalizerCandidate (f , g)) +-𝒰 (hasCoequalizer f g)
  unify-ℒHMTypes f g = unify f g


infixl 80 _⇃[_]⇂

abstract
  _⇃[_]⇂ : ∀{a b : ℒHMTypes} -> 𝒯⊔Term 𝒹 ⟨ a ⟩ tt -> (a ⟶ b) -> 𝒯⊔Term 𝒹 ⟨ b ⟩ tt
  _⇃[_]⇂ x f = subst-⧜𝐒𝐮𝐛𝐬𝐭 f tt x

-- //




-- [Hide]


module _ {a b c : ℒHMTypes} where
  functoriality-◆-⇃[]⇂ : ∀{τ : ℒHMType ⟨ a ⟩} -> {f : a ⟶ b} -> {g : b ⟶ c}
                          -> τ ⇃[ f ]⇂ ⇃[ g ]⇂ ≡ τ ⇃[ f ◆ g ]⇂
  functoriality-◆-⇃[]⇂ = {!!}

module _ {a : ℒHMTypes} where
  functoriality-id-⇃[]⇂ : ∀{τ : ℒHMType ⟨ a ⟩} -> τ ⇃[ id ]⇂ ≡ τ
  functoriality-id-⇃[]⇂ = {!!}

-- //
