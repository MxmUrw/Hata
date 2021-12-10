
module Verification.Core.Data.Language.HindleyMilner.Variant.Classical.Typed.Context.Properties where


open import Verification.Conventions hiding (ℕ ; _⊔_)


open import Verification.Core.Data.Language.HindleyMilner.Variant.Classical.Typed.Imports


open import Verification.Core.Data.Language.HindleyMilner.Helpers
open import Verification.Core.Data.Language.HindleyMilner.Type.Variant.FreeFiniteCoproductTheoryTerm.Signature
open import Verification.Core.Data.Language.HindleyMilner.Type.Variant.FreeFiniteCoproductTheoryTerm.Definition
open import Verification.Core.Data.Language.HindleyMilner.Variant.Classical.Typed.Context.Definition





map-ℒHMCtx : ∀{n : ♮ℕ} -> {q : ℒHMQuant n} {a b : ℒHMTypes} -> a ⟶ b -> ℒHMCtx q a -> ℒHMCtx q b
map-ℒHMCtx f [] = []
map-ℒHMCtx f (c ∷ xs) = (c ⇃[ f ⇃⊔⇂ id ]⇂) ∷ (map-ℒHMCtx f xs)




infixl 80 _⇃[_]⇂ᶜ

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



