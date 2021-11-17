
module Verification.Core.Data.Language.HindleyMilner.Type.Definition where

open import Verification.Conventions hiding (lookup ; ℕ ; _⊔_)
open import Verification.Core.Set.Discrete
open import Verification.Core.Algebra.Monoid.Definition
open import Verification.Core.Algebra.Monoid.Free
open import Verification.Core.Data.AllOf.Collection.Basics
open import Verification.Core.Data.AllOf.Collection.TermTools
open import Verification.Core.Category.Std.AllOf.Collection.Basics
open import Verification.Core.Category.Std.AllOf.Collection.Limits

open import Verification.Core.Theory.Std.Specific.ProductTheory.Module
open import Verification.Core.Theory.Std.Specific.ProductTheory.Instance.hasBoundaries

ProductTheoryData = 𝕋×.統.𝒜


-------------------------------------------------
-- Definition of the data for the HM types

-- data 𝒹₀ : 𝒰₀ where
--   tyᵗ : 𝒹₀

𝒹₀ : 𝒰₀
𝒹₀ = ⊤-𝒰

pattern tyᵗ = tt

-- instance
--   isDiscrete:𝒹₀ : isDiscrete 𝒹₀
--   isDiscrete:𝒹₀ = record { _≟-Str_ = lem-1 }
--     where
--       lem-1 : (a b : 𝒹₀) → Decision (a ≡-Str b)
--       lem-1 tyᵗ tyᵗ = yes refl-≣

data 𝒹₁ : List 𝒹₀ → 𝒹₀ → 𝒰 ℓ₀ where
  ⇒ᵗ : 𝒹₁ (tyᵗ ∷ tyᵗ ∷ []) tyᵗ
  ℕᵗ : 𝒹₁ [] tyᵗ
  𝔹ᵗ : 𝒹₁ [] tyᵗ

instance
  isDiscrete:𝒹₁ : ∀{xs : List 𝒹₀} {x : 𝒹₀} -> isDiscrete (𝒹₁ xs x)
  isDiscrete:𝒹₁ {xs} {x} = record { _≟-Str_ = lem-1 }
    where
      lem-1 : (a b : 𝒹₁ xs x) → Decision (a ≡-Str b)
      lem-1 ⇒ᵗ ⇒ᵗ = yes refl-≣
      lem-1 ℕᵗ ℕᵗ = yes refl-≣
      lem-1 ℕᵗ 𝔹ᵗ = no (λ ())
      lem-1 𝔹ᵗ ℕᵗ = no (λ ())
      lem-1 𝔹ᵗ 𝔹ᵗ = yes refl-≣

instance
  isSet:𝒹₀ : isSet-Str (𝒹₀)
  isSet:𝒹₀ = {!!}

infixr 30 _⇒_
pattern _⇒_ a b = con ⇒ᵗ (incl a ⋆-⧜ (incl b ⋆-⧜ ◌-⧜))

𝒹 : ProductTheoryData _
𝒹 = record { Sort = 𝒹₀ ; Con = 𝒹₁ }


ℒHMType : (Γ : 人ℕ) -> 𝒰₀
ℒHMType Γ = Term₁-𝕋× 𝒹 Γ tt



ℒHMTypesᵘ : 𝒰₀
ℒHMTypesᵘ = ⧜𝐒𝐮𝐛𝐬𝐭 ′ Term-𝕋× 𝒹 ′

macro ℒHMTypes = #structureOn ℒHMTypesᵘ

st : ℒHMTypes
st = incl (incl tt)

infix 25 ∀[_]_
record ℒHMPolyTypeᵘ (a : ℒHMTypes) : 𝒰₀ where
  constructor ∀[_]_
  field fst : ℒHMTypes
  field snd : ℒHMType ⟨ a ⊔ fst ⟩
  -- Term₁-𝕋× 𝒹 ⟨ (a ⊔ fst) ⟩ tt

open ℒHMPolyTypeᵘ public

macro ℒHMPolyType = #structureOn ℒHMPolyTypeᵘ

_⇃[_]⇂ : ∀{a b : ℒHMTypes} -> Term₁-𝕋× 𝒹 ⟨ a ⟩ tt -> (a ⟶ b) -> Term₁-𝕋× 𝒹 ⟨ b ⟩ tt
_⇃[_]⇂ x f = subst-⧜𝐒𝐮𝐛𝐬𝐭 f tt x


module _ {a : ℒHMTypes} where
  record ℒHMPolyTypeHom (α β : ℒHMPolyType a) : 𝒰₀ where
    field fst : fst α ⟶ fst β
    field snd : snd α ⇃[ id ⇃⊔⇂ fst ]⇂ ≡ snd β

instance
  isCategory:ℒHMPolyType : ∀{a} -> isCategory {ℓ₀ , ℓ₀} (ℒHMPolyType a)
  isCategory.Hom isCategory:ℒHMPolyType = ℒHMPolyTypeHom
  isCategory.isSetoid:Hom isCategory:ℒHMPolyType = {!!}
  isCategory.id isCategory:ℒHMPolyType = {!!}
  isCategory._◆_ isCategory:ℒHMPolyType = {!!}
  isCategory.unit-l-◆ isCategory:ℒHMPolyType = {!!}
  isCategory.unit-r-◆ isCategory:ℒHMPolyType = {!!}
  isCategory.unit-2-◆ isCategory:ℒHMPolyType = {!!}
  isCategory.assoc-l-◆ isCategory:ℒHMPolyType = {!!}
  isCategory.assoc-r-◆ isCategory:ℒHMPolyType = {!!}
  isCategory._◈_ isCategory:ℒHMPolyType = {!!}




map-ℒHMPolyType : ∀{a b : ℒHMTypes} -> a ⟶ b -> ℒHMPolyType a ⟶ ℒHMPolyType b
map-ℒHMPolyType σ (∀[ v ] x) = ∀[ v ] (x ⇃[ σ ⇃⊔⇂ id ]⇂)

instance
  isFunctor:ℒHMPolyTypeᵘ : isFunctor ℒHMTypes 𝐔𝐧𝐢𝐯₀ ℒHMPolyType
  isFunctor.map isFunctor:ℒHMPolyTypeᵘ = map-ℒHMPolyType
  isFunctor.isSetoidHom:map isFunctor:ℒHMPolyTypeᵘ = {!!}
  isFunctor.functoriality-id isFunctor:ℒHMPolyTypeᵘ = {!!}
  isFunctor.functoriality-◆ isFunctor:ℒHMPolyTypeᵘ = {!!}


ℒHMCtxᵘ : ℒHMTypes -> 𝐔𝐧𝐢𝐯₀
ℒHMCtxᵘ = 人List ∘ ℒHMPolyType

macro ℒHMCtx = #structureOn ℒHMCtxᵘ

instance
  isFunctor:ℒHMCtx : isFunctor ℒHMTypes 𝐔𝐧𝐢𝐯₀ ℒHMCtx
  isFunctor:ℒHMCtx = {!!}

-- TODO: move this into a collection
open import Verification.Core.Category.Std.Limit.Specific.Coproduct.Properties.Monoidal

abstr : ∀{m n : ℒHMTypes} -> ℒHMPolyType (m ⊔ n) -> ℒHMPolyType m
abstr {m} {n} (∀[ v ] x) = ∀[ (n ⊔ v) ] (x ⇃[ ⟨ assoc-l-⊔ ⟩ ]⇂)

{-
-}

