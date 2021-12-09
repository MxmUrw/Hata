
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

open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Category.Std.Limit.Specific.Coequalizer
open import Verification.Core.Category.Std.Limit.Specific.Coproduct.Definition
open import Verification.Core.Category.Std.Limit.Specific.Coproduct.Instance.Functor
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


-- module _ (n : ♮ℕ) (m : ℒHMTypes) where
--   ℒHMCtxᵘ = Listᴰ (const (ℒHMPolyType m)) n

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

infixl 80 _⇃[_]⇂-Ctx
_⇃[_]⇂-Ctx : ∀{k} -> ∀{a b : ℒHMTypes} -> ℒHMCtx k a -> (a ⟶ b) -> ℒHMCtx k b
_⇃[_]⇂-Ctx x f = map-ℒHMCtx f x

_⇃[_]⇂-CtxFor : ∀{k} -> ∀{a b : ℒHMTypes} -> {Q : ℒHMQuant k} -> ℒHMCtxFor Q a -> (a ⟶ b) -> ℒHMCtxFor Q b
_⇃[_]⇂-CtxFor x f = map-ℒHMCtxFor f x



abstract
  _⇃[≀_≀]⇂-Ctx : ∀{k} -> ∀{a b : ℒHMTypes} -> (Γ : ℒHMCtx k a) -> {f g : a ⟶ b}
                -> f ∼ g -> Γ ⇃[ f ]⇂-Ctx ≡ Γ ⇃[ g ]⇂-Ctx
  _⇃[≀_≀]⇂-Ctx Γ {f = f} {g} p =
    let p' : map-ℒHMCtx f ≡ map-ℒHMCtx g
        p' = cong-∼ p
    in funExt⁻¹ p' Γ

  _⇃[≀_≀]⇂-CtxFor : ∀{k} {Q : ℒHMQuant k} -> ∀{a b : ℒHMTypes} -> (Γ : ℒHMCtxFor Q a) -> {f g : a ⟶ b}
                -> f ∼ g -> Γ ⇃[ f ]⇂-CtxFor ≡ Γ ⇃[ g ]⇂-CtxFor
  _⇃[≀_≀]⇂-CtxFor Γ {f = f} {g} p = {!!}

  _⇃[≀_≀]⇂ : ∀{a b : ℒHMTypes} -> (Γ : ℒHMType ⟨ a ⟩) -> {f g : a ⟶ b}
                -> f ∼ g -> Γ ⇃[ f ]⇂ ≡ Γ ⇃[ g ]⇂
  _⇃[≀_≀]⇂ Γ {f = f} {g} p = {!!}
    -- let p' : map-ℒHMCtx f ≡ map-ℒHMCtx g
    --     p' = cong-∼ p
    -- in funExt⁻¹ p' Γ

  module _ {k} {a b c : ℒHMTypes} where
    functoriality-◆-⇃[]⇂-Ctx : ∀{Γ : ℒHMCtx k a} -> {f : a ⟶ b} -> {g : b ⟶ c}
                            -> Γ ⇃[ f ]⇂-Ctx ⇃[ g ]⇂-Ctx ≡ Γ ⇃[ f ◆ g ]⇂-Ctx
    functoriality-◆-⇃[]⇂-Ctx = {!!}

  module _ {k} {Q : ℒHMQuant k} {a b c : ℒHMTypes} where
    functoriality-◆-⇃[]⇂-CtxFor : ∀{Γ : ℒHMCtxFor Q a} -> {f : a ⟶ b} -> {g : b ⟶ c}
                            -> Γ ⇃[ f ]⇂-CtxFor ⇃[ g ]⇂-CtxFor ≡ Γ ⇃[ f ◆ g ]⇂-CtxFor
    functoriality-◆-⇃[]⇂-CtxFor = {!!}

  module _ {k} {Q : ℒHMQuant k} {a : ℒHMTypes} where

    functoriality-id-⇃[]⇂-CtxFor : ∀{Γ : ℒHMCtxFor Q a} -> Γ ⇃[ id ]⇂-CtxFor ≡ Γ
    functoriality-id-⇃[]⇂-CtxFor = {!!}



_⇃[_]⇂ᶜ = _⇃[_]⇂-CtxFor
_⇃[≀_≀]⇂ᶜ = _⇃[≀_≀]⇂-CtxFor

module §-ℒHMCtx where



  abstract
    prop-2 : ∀{μs νs : ℒHMTypes}
            -> ∀{k i} -> {Q : ℒHMQuant k}
            -> {Γ : ℒHMCtxFor Q μs} -> (k∍i : k ∍♮ i)
            -> ∀ (σ₀ : μs ⟶ νs)
            -> ∀ (σ₁ : lookup-Listᴰ Q k∍i ⟶ νs)
            ->  lookup-Listᴰ² (Γ ⇃[ σ₀ ]⇂-CtxFor) k∍i ⇃[ ⦗ id , σ₁ ⦘ ]⇂
              ≡
                lookup-Listᴰ² Γ k∍i ⇃[ ⦗ σ₀ , σ₁ ⦘ ]⇂
    prop-2 {Γ = b ∷ Γ} incl σ₀ σ₁ =
      let lem-0 : (σ₀ ⇃⊔⇂ id) ◆ ⦗ id , σ₁ ⦘ ∼ ⦗ σ₀ , σ₁ ⦘
          lem-0 = (σ₀ ⇃⊔⇂ id) ◆ ⦗ id , σ₁ ⦘   ⟨ append-⇃⊔⇂ {f0 = σ₀} {id} {id} {σ₁} ⟩-∼
                  ⦗ σ₀ ◆ id , id ◆ σ₁ ⦘       ⟨ cong-∼ {{isSetoidHom:⦗⦘}} (unit-r-◆ {f = σ₀} , unit-l-◆ {f = σ₁}) ⟩-∼
                  ⦗ σ₀ , σ₁ ⦘                 ∎

          lem-1 : b ⇃[ σ₀ ⇃⊔⇂ id ]⇂ ⇃[ ⦗ id , σ₁ ⦘ ]⇂ ≡ b ⇃[ ⦗ σ₀ , σ₁ ⦘ ]⇂
          lem-1 = b ⇃[ σ₀ ⇃⊔⇂ id ]⇂ ⇃[ ⦗ id , σ₁ ⦘ ]⇂    ⟨ functoriality-◆-⇃[]⇂ {τ = b} {f = (σ₀ ⇃⊔⇂ id)} {g = ⦗ id , σ₁ ⦘} ⟩-≡
                  b ⇃[ (σ₀ ⇃⊔⇂ id) ◆ ⦗ id , σ₁ ⦘ ]⇂      ⟨ b ⇃[≀ lem-0 ≀]⇂ ⟩-≡
                  b ⇃[ ⦗ σ₀ , σ₁ ⦘ ]⇂                    ∎-≡
      in {!!}
      --  lem-1
    prop-2 {Γ = b ∷ Γ} (skip k∍i) σ₀ σ₁ = {!!}
    -- prop-2 {Γ = Γ} k∍i σ₀ σ₁

    prop-3 : ∀{μs νs : ℒHMTypes}
            -> ∀{k i} -> {Q : ℒHMQuant k}
            -> {Γ : ℒHMCtxFor Q μs} -> (k∍i : k ∍♮ i)
            -> ∀ (σ : μs ⊔ lookup-Listᴰ Q k∍i ⟶ νs)
            ->  lookup-Listᴰ² (Γ ⇃[ ι₀ ◆ σ ]⇂-CtxFor) k∍i ⇃[ ⦗ id , ι₁ ◆ σ ⦘ ]⇂
              ≡
                lookup-Listᴰ² Γ k∍i ⇃[ σ ]⇂
    prop-3 = {!!}


