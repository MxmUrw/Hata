
module Verification.Core.Data.Language.HindleyMilner.Variant.Classical.Typed.Context.Properties where


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
-- open import Verification.Core.Category.Std.Limit.Specific.Coproduct.Definition
open import Verification.Core.Category.Std.Limit.Specific.Coproduct.Instance.Functor
  -- using (append-⇃⊔⇂)
open import Verification.Core.Computation.Unification.Definition

open import Verification.Core.Theory.Std.Specific.FreeFiniteCoproductTheory.Param
open import Verification.Core.Theory.Std.Specific.FreeFiniteCoproductTheory.Definition
open import Verification.Core.Theory.Std.Specific.FreeFiniteCoproductTheory.Instance.Functor
open import Verification.Core.Theory.Std.Specific.FreeFiniteCoproductTheory.Instance.RelativeMonad
open import Verification.Core.Theory.Std.Specific.FreeFiniteCoproductTheory.Unification

open import Verification.Core.Data.Language.HindleyMilner.Helpers
open import Verification.Core.Data.Language.HindleyMilner.Type.Variant.FreeFiniteCoproductTheoryTerm.Signature
open import Verification.Core.Data.Language.HindleyMilner.Type.Variant.FreeFiniteCoproductTheoryTerm.Definition
open import Verification.Core.Data.Language.HindleyMilner.Variant.Classical.Typed.Context.Definition


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

-- {-# DISPLAY isCoequalizer.π₌ _ = π #-}
-- {-# DISPLAY isCoproduct.ι₀ _ = ι₀ #-}
-- {-# DISPLAY isCoproduct.ι₁ _ = ι₁ #-}
{-# DISPLAY _内◆-⧜𝐒𝐮𝐛𝐬𝐭_ f g = f ◆ g #-}
{-# DISPLAY 内id-⧜𝐒𝐮𝐛𝐬𝐭 = id #-}



map-ℒHMCtx : ∀{n : ♮ℕ} -> {q : ℒHMQuant n} {a b : ℒHMTypes} -> a ⟶ b -> ℒHMCtx q a -> ℒHMCtx q b
map-ℒHMCtx f [] = []
map-ℒHMCtx f (c ∷ xs) = (c ⇃[ f ⇃⊔⇂ id ]⇂) ∷ (map-ℒHMCtx f xs)

isSetoidHom:map-ℒHMCtx : ∀{n : ♮ℕ} {q : ℒHMQuant n} -> {a b : ℒHMTypes} -> {f g : a ⟶ b}
                        -> (f ∼ g) -> map-ℒHMCtx {q = q} f ≡ map-ℒHMCtx g
isSetoidHom:map-ℒHMCtx {q = q} {f = f} {g}  p = funExt lem-0
  where
    lem-0 : ∀ x -> map-ℒHMCtx {q = q} f x ≡ map-ℒHMCtx g x
    lem-0 [] = refl-≡
    lem-0 (c ∷ x) = {!!}


-- instance
--   isSetoidHom:map-ℒHMCtx : ∀{n : ♮ℕ} -> {a b : ℒHMTypes}
--                             -> isSetoidHom (a ⟶ b) ((ℒHMCtx n a -> ℒHMCtx n b) since isSetoid:byPath) map-ℒHMCtx
--   isSetoidHom:map-ℒHMCtx = record { cong-∼ = isSetoidHom:map-ℒHMCtx-2 }


-- instance
--   isFunctor:ℒHMCtx  : ∀{n} -> isFunctor ℒHMTypes 𝐔𝐧𝐢𝐯₀ (ℒHMCtx n)
--   isFunctor.map isFunctor:ℒHMCtx = map-ℒHMCtx
--   isFunctor.isSetoidHom:map isFunctor:ℒHMCtx = it
--   isFunctor.functoriality-id isFunctor:ℒHMCtx = {!!}
--   isFunctor.functoriality-◆ isFunctor:ℒHMCtx = {!!}

infixl 80 _⇃[_]⇂ᶜ
-- _⇃[_]⇂-Ctx : ∀{k} -> ∀{a b : ℒHMTypes} -> ℒHMCtx k a -> (a ⟶ b) -> ℒHMCtx k b
-- _⇃[_]⇂-Ctx x f = map-ℒHMCtx f x

_⇃[_]⇂ᶜ : ∀{k} -> ∀{a b : ℒHMTypes} -> {Q : ℒHMQuant k} -> ℒHMCtx Q a -> (a ⟶ b) -> ℒHMCtx Q b
_⇃[_]⇂ᶜ x f = map-ℒHMCtx f x




abstract
  _⇃[≀_≀]⇂ᶜ : ∀{k} {Q : ℒHMQuant k} -> ∀{a b : ℒHMTypes} -> (Γ : ℒHMCtx Q a) -> {f g : a ⟶ b}
                -> f ∼ g -> Γ ⇃[ f ]⇂ᶜ ≡ Γ ⇃[ g ]⇂ᶜ
  _⇃[≀_≀]⇂ᶜ [] {f = f} {g} p = refl-≡
  _⇃[≀_≀]⇂ᶜ (c ∷ Γ) {f = f} {g} p = λ i -> (c ⇃[≀ p ≀⇃⊔⇂≀ refl-StrId {x = id} ≀]⇂) i ∷ (Γ ⇃[≀ p ≀]⇂ᶜ) i


  module _ {a b c : ℒHMTypes} where
    functoriality-◆-⇃[]⇂ᶜ : ∀{k} {Q : ℒHMQuant k} {Γ : ℒHMCtx Q a} -> {f : a ⟶ b} -> {g : b ⟶ c}
                            -> Γ ⇃[ f ]⇂ᶜ ⇃[ g ]⇂ᶜ ≡ Γ ⇃[ f ◆ g ]⇂ᶜ
    functoriality-◆-⇃[]⇂ᶜ {Γ = []} = refl-≡
    functoriality-◆-⇃[]⇂ᶜ {Q = _ ∷ _} {Γ = c ∷ Γ} {f = f} {g = g} = λ i → (lem-2 i) ∷ (functoriality-◆-⇃[]⇂ᶜ {Γ = Γ} {f = f} {g = g}) i
      where
        lem-2 : c ⇃[ f ⇃⊔⇂ id ]⇂ ⇃[ g ⇃⊔⇂ id ]⇂ ≡ c ⇃[ (f ◆ g) ⇃⊔⇂ id ]⇂
        lem-2 = c ⇃[ f ⇃⊔⇂ id ]⇂ ⇃[ g ⇃⊔⇂ id ]⇂   ⟨ functoriality-◆-⇃[]⇂ {τ = c} {f = f ⇃⊔⇂ id} {g = g ⇃⊔⇂ id} ⟩-≡
                c ⇃[ (f ⇃⊔⇂ id) ◆ (g ⇃⊔⇂ id) ]⇂   ⟨ c ⇃[≀ functoriality-◆-⊔ ⁻¹ ≀]⇂ ⟩-≡
                c ⇃[ ((f ◆ g) ⇃⊔⇂ (id ◆ id)) ]⇂       ⟨ c ⇃[≀ refl ≀⇃⊔⇂≀ unit-2-◆ ≀]⇂ ⟩-≡
                c ⇃[ (f ◆ g) ⇃⊔⇂ id ]⇂            ∎-≡

  module _ {a : ℒHMTypes} where
    functoriality-id-⇃[]⇂ᶜ : ∀{k} {Q : ℒHMQuant k} {Γ : ℒHMCtx Q a} -> Γ ⇃[ id ]⇂ᶜ ≡ Γ
    functoriality-id-⇃[]⇂ᶜ {Γ = []} = refl-≡
    functoriality-id-⇃[]⇂ᶜ {Γ = c ∷ Γ} = λ i -> lem-2 i ∷ functoriality-id-⇃[]⇂ᶜ {Γ = Γ} i
      where
        lem-2 : c ⇃[ id ⇃⊔⇂ id ]⇂ ≡ c
        lem-2 = c ⇃[ id ⇃⊔⇂ id ]⇂   ⟨ c ⇃[≀ functoriality-id-⊔ ≀]⇂ ⟩-≡
                c ⇃[ id ]⇂          ⟨ functoriality-id-⇃[]⇂ ⟩-≡
                c                   ∎-≡



module §-ℒHMCtx where



  abstract
    prop-2 : ∀{μs νs : ℒHMTypes}
            -> ∀{k i} -> {Q : ℒHMQuant k}
            -> {Γ : ℒHMCtx Q μs} -> (k∍i : k ∍♮ i)
            -> ∀ (σ₀ : μs ⟶ νs)
            -> ∀ (σ₁ : lookup-Listᴰ Q k∍i ⟶ νs)
            ->  lookup-Listᴰ² (Γ ⇃[ σ₀ ]⇂ᶜ) k∍i ⇃[ ⦗ id , σ₁ ⦘ ]⇂
              ≡
                lookup-Listᴰ² Γ k∍i ⇃[ ⦗ σ₀ , σ₁ ⦘ ]⇂
    prop-2 {Γ = b ∷ Γ} incl σ₀ σ₁ = {!!}
      -- let lem-0 : (σ₀ ⇃⊔⇂ id) ◆ ⦗ id , σ₁ ⦘ ∼ ⦗ σ₀ , σ₁ ⦘
      --     lem-0 = (σ₀ ⇃⊔⇂ id) ◆ ⦗ id , σ₁ ⦘   ⟨ append-⇃⊔⇂ {f0 = σ₀} {id} {id} {σ₁} ⟩-∼
      --             ⦗ σ₀ ◆ id , id ◆ σ₁ ⦘       ⟨ cong-∼ {{isSetoidHom:⦗⦘}} (unit-r-◆ {f = σ₀} , unit-l-◆ {f = σ₁}) ⟩-∼
      --             ⦗ σ₀ , σ₁ ⦘                 ∎

      --     lem-1 : b ⇃[ σ₀ ⇃⊔⇂ id ]⇂ ⇃[ ⦗ id , σ₁ ⦘ ]⇂ ≡ b ⇃[ ⦗ σ₀ , σ₁ ⦘ ]⇂
      --     lem-1 = b ⇃[ σ₀ ⇃⊔⇂ id ]⇂ ⇃[ ⦗ id , σ₁ ⦘ ]⇂    ⟨ functoriality-◆-⇃[]⇂ {τ = b} {f = (σ₀ ⇃⊔⇂ id)} {g = ⦗ id , σ₁ ⦘} ⟩-≡
      --             b ⇃[ (σ₀ ⇃⊔⇂ id) ◆ ⦗ id , σ₁ ⦘ ]⇂      ⟨ b ⇃[≀ lem-0 ≀]⇂ ⟩-≡
      --             b ⇃[ ⦗ σ₀ , σ₁ ⦘ ]⇂                    ∎-≡
      -- in {!!}
      --  lem-1
    prop-2 {Γ = b ∷ Γ} (skip k∍i) σ₀ σ₁ = {!!}
    -- prop-2 {Γ = Γ} k∍i σ₀ σ₁

{-
    prop-3 : ∀{μs νs : ℒHMTypes}
            -> ∀{k i} -> {Q : ℒHMQuant k}
            -> {Γ : ℒHMCtx Q μs} -> (k∍i : k ∍♮ i)
            -> ∀ (σ : μs ⊔ lookup-Listᴰ Q k∍i ⟶ νs)
            ->  lookup-Listᴰ² (Γ ⇃[ ι₀ ◆ σ ]⇂ᶜ) k∍i ⇃[ ⦗ id , ι₁ ◆ σ ⦘ ]⇂
              ≡
                lookup-Listᴰ² Γ k∍i ⇃[ σ ]⇂
    prop-3 = {!!}

-}
