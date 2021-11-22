
module Verification.Core.Data.Language.HindleyMilner.Type.Definition where

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

open import Verification.Core.Data.Language.HindleyMilner.Helpers

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
  field fst : ♮𝐒𝐮𝐛𝐬𝐭 ′ Term-𝕋× 𝒹 ′
  field snd : ℒHMType ⟨ a ⊔ (ι fst) ⟩
  -- Term₁-𝕋× 𝒹 ⟨ (a ⊔ fst) ⟩ tt

open ℒHMPolyTypeᵘ public

macro ℒHMPolyType = #structureOn ℒHMPolyTypeᵘ

asArr : ∀ {a} -> ℒHMType ⟨ a ⟩ -> st ⟶ a
asArr t = ⧜subst (incl t)

fromArr : ∀ {a} -> st ⟶ a -> ℒHMType ⟨ a ⟩
fromArr (⧜subst (incl x)) = x

abstract
  unify-ℒHMTypes : ∀{a b : ℒHMTypes} -> (f g : a ⟶ b) -> (¬ hasCoequalizerCandidate (f , g)) +-𝒰 (hasCoequalizer f g)
  unify-ℒHMTypes f g = unify f g

_⇃[_]⇂ : ∀{a b : ℒHMTypes} -> Term₁-𝕋× 𝒹 ⟨ a ⟩ tt -> (a ⟶ b) -> Term₁-𝕋× 𝒹 ⟨ b ⟩ tt
_⇃[_]⇂ x f = subst-⧜𝐒𝐮𝐛𝐬𝐭 f tt x


_⇃[_]⇂-poly : ∀{a b : ℒHMTypes} -> ℒHMPolyType a -> (a ⟶ b) -> ℒHMPolyType b
_⇃[_]⇂-poly (∀[ vs ] α) f = ∀[ vs ] (α ⇃[ f ⇃⊔⇂ id ]⇂)

module _ {a : ℒHMTypes} where
  record ℒHMPolyTypeHom (α β : ℒHMPolyType a) : 𝒰₀ where
    field fst : ι (fst α) ⟶ ι (fst β)
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



-----------------------------------------
-- Ctx'

ℒHMQuant : (k : ♮ℕ) -> 𝒰₀
ℒHMQuant = DList (const (ℒHMTypes))

ℒHMCtxFor : ∀{k} -> (q : ℒHMQuant k) -> ∀ μs -> 𝒰₀
ℒHMCtxFor q μs = DDList (λ a -> ℒHMType ⟨ μs ⊔ a ⟩) q

ℒHMCtx : (k : ♮ℕ) -> (μs : ℒHMTypes) -> 𝒰₀
ℒHMCtx k μs = ∑ λ (q : ℒHMQuant k) -> ℒHMCtxFor q μs


-- module _ (n : ♮ℕ) (m : ℒHMTypes) where
--   ℒHMCtxᵘ = DList (const (ℒHMPolyType m)) n

-- module _ (n : ♮ℕ) where
--   macro ℒHMCtx = #structureOn (ℒHMCtxᵘ n)

map-ℒHMCtxFor : ∀{n : ♮ℕ} -> {q : ℒHMQuant n} {a b : ℒHMTypes} -> a ⟶ b -> ℒHMCtxFor q a ⟶ ℒHMCtxFor q b
map-ℒHMCtxFor f [] = []
map-ℒHMCtxFor f (c ∷ xs) = (c ⇃[ f ⇃⊔⇂ id ]⇂) ∷ (map-ℒHMCtxFor f xs)

map-ℒHMCtx : ∀{n : ♮ℕ} -> {a b : ℒHMTypes} -> a ⟶ b -> ℒHMCtx n a ⟶ ℒHMCtx n b
map-ℒHMCtx f (q , Γ) = q , map-ℒHMCtxFor f Γ

-- map-ℒHMCtx f ([] , []) = [] , []
-- map-ℒHMCtx f (b ∷ bs , c ∷ cs) = (b ∷ bs) , (mapOf ℒHMPolyType f b) ∷ map-ℒHMCtx f x

isSetoidHom:map-ℒHMCtx-2 : ∀{n : ♮ℕ} -> {a b : ℒHMTypes} -> {f g : a ⟶ b}
                          -> (f ∼ g) -> map-ℒHMCtx {n = n} f ≡ map-ℒHMCtx g
isSetoidHom:map-ℒHMCtx-2 = {!!}

instance
  isSetoidHom:map-ℒHMCtx : ∀{n : ♮ℕ} -> {a b : ℒHMTypes}
                            -> isSetoidHom (a ⟶ b) ((ℒHMCtx n a -> ℒHMCtx n b) since isSetoid:byPath) map-ℒHMCtx
  isSetoidHom:map-ℒHMCtx = record { cong-∼ = isSetoidHom:map-ℒHMCtx-2 }


-- instance
--   isFunctor:ℒHMCtx  : ∀{n} -> isFunctor ℒHMTypes 𝐔𝐧𝐢𝐯₀ (ℒHMCtx n)
--   isFunctor.map isFunctor:ℒHMCtx = map-ℒHMCtx
--   isFunctor.isSetoidHom:map isFunctor:ℒHMCtx = it
--   isFunctor.functoriality-id isFunctor:ℒHMCtx = {!!}
--   isFunctor.functoriality-◆ isFunctor:ℒHMCtx = {!!}

infixl 80 _⇃[_]⇂-Ctx _⇃[_]⇂
_⇃[_]⇂-Ctx : ∀{k} -> ∀{a b : ℒHMTypes} -> ℒHMCtx k a -> (a ⟶ b) -> ℒHMCtx k b
_⇃[_]⇂-Ctx x f = map-ℒHMCtx f x

_⇃[_]⇂-CtxFor : ∀{k} -> ∀{a b : ℒHMTypes} -> {Q : ℒHMQuant k} -> ℒHMCtxFor Q a -> (a ⟶ b) -> ℒHMCtxFor Q b
_⇃[_]⇂-CtxFor x f = map-ℒHMCtxFor f x

_⇃[≀_≀]⇂-Ctx : ∀{k} -> ∀{a b : ℒHMTypes} -> (Γ : ℒHMCtx k a) -> {f g : a ⟶ b}
              -> f ∼ g -> Γ ⇃[ f ]⇂-Ctx ≡ Γ ⇃[ g ]⇂-Ctx
_⇃[≀_≀]⇂-Ctx Γ {f = f} {g} p =
  let p' : map-ℒHMCtx f ≡ map-ℒHMCtx g
      p' = cong-∼ p
  in funExt⁻¹ p' Γ

module _ {k} {a b c : ℒHMTypes} where
  functoriality-⇃[]⇂-Ctx : ∀{Γ : ℒHMCtx k a} -> {f : a ⟶ b} -> {g : b ⟶ c}
                           -> Γ ⇃[ f ]⇂-Ctx ⇃[ g ]⇂-Ctx ≡ Γ ⇃[ f ◆ g ]⇂-Ctx
  functoriality-⇃[]⇂-Ctx = {!!}


module _ {a b c : ℒHMTypes} where
  functoriality-⇃[]⇂ : ∀{τ : ℒHMType ⟨ a ⟩} -> {f : a ⟶ b} -> {g : b ⟶ c}
                           -> τ ⇃[ f ]⇂ ⇃[ g ]⇂ ≡ τ ⇃[ f ◆ g ]⇂
  functoriality-⇃[]⇂ = {!!}

{-

-}

-- TODO: move this into a collection
open import Verification.Core.Category.Std.Limit.Specific.Coproduct.Properties.Monoidal

abstr : ∀{m n : ℒHMTypes} -> ℒHMPolyType (m ⊔ n) -> ℒHMPolyType m
abstr {m} {n} (∀[ v ] x) = {!!} --  ∀[ (n ⊔ v) ] (x ⇃[ ⟨ assoc-l-⊔ ⟩ ]⇂)

-- abstr : ∀{m n : ℒHMTypes} -> ℒHMPolyType (m ⊔ n) -> ℒHMPolyType m
-- abstr {m} {n} (∀[ v ] x) = ∀[ (n ⊔ v) ] (x ⇃[ ⟨ assoc-l-⊔ ⟩ ]⇂)

{-
-}

