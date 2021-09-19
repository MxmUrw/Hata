
module Verification.Experimental.Theory.Std.Specific.LambdaCalculus.Definition where

open import Verification.Conventions hiding (_⊔_)

open import Verification.Experimental.Set.Discrete
open import Verification.Experimental.Algebra.Monoid.Definition
open import Verification.Experimental.Algebra.Monoid.Free
open import Verification.Experimental.Algebra.Monoid.Free.Element
open import Verification.Experimental.Category.Std.Category.Definition
open import Verification.Experimental.Data.Substitution.Definition

open import Verification.Experimental.Computation.Unification.Definition
open import Verification.Experimental.Theory.Std.Specific.ProductTheory.Definition
open import Verification.Experimental.Theory.Std.Specific.ProductTheory.Instance.PCF
open import Verification.Experimental.Theory.Std.Presentation.Token.Definition
open import Verification.Experimental.Theory.Std.Specific.ProductTheory.Instance.FromString


data Sort-𝕋Λ : 𝒰₀ where
  tyᵗ ctxᵗ : Sort-𝕋Λ

instance
  isDiscrete:Sort-𝕋Λ : isDiscrete Sort-𝕋Λ
  isDiscrete:Sort-𝕋Λ = {!!}

data Con-Type-𝕋× : List Sort-𝕋Λ → Sort-𝕋Λ → 𝒰 ℓ₀ where
  ⇒ᵗ : Con-Type-𝕋× (tyᵗ ∷ tyᵗ ∷ []) tyᵗ
  ℕᵗ : Con-Type-𝕋× [] tyᵗ
  𝔹ᵗ : Con-Type-𝕋× [] tyᵗ
  []ᵗ : Con-Type-𝕋× [] ctxᵗ
  ▻ᵗ : Con-Type-𝕋× (ctxᵗ ∷ tyᵗ ∷ []) ctxᵗ

private
  lem-1 : ∀{xs : List Sort-𝕋Λ} {x : Sort-𝕋Λ} -> (a b : Con-Type-𝕋× xs x) -> Decision (a ≣ b)
  lem-1 ⇒ᵗ ⇒ᵗ = yes refl-≣
  lem-1 ℕᵗ ℕᵗ = yes refl-≣
  lem-1 ℕᵗ 𝔹ᵗ = no (λ ())
  lem-1 𝔹ᵗ ℕᵗ = no (λ ())
  lem-1 𝔹ᵗ 𝔹ᵗ = yes refl-≣
  lem-1 []ᵗ []ᵗ = yes refl-≣
  lem-1 ▻ᵗ ▻ᵗ = yes refl-≣


TypeAxiom-𝕋Λ : ProductTheory ℓ₀
Sort TypeAxiom-𝕋Λ = Sort-𝕋Λ
isDiscrete:Sort TypeAxiom-𝕋Λ = {!!}
isSet-Str:Sort TypeAxiom-𝕋Λ = {!!}
Con TypeAxiom-𝕋Λ = Con-Type-𝕋×
isDiscrete:Con TypeAxiom-𝕋Λ = record { _≟-Str_ = lem-1 }

Type-𝕋Λ : 𝒰₀
Type-𝕋Λ = Term₁-𝕋× TypeAxiom-𝕋Λ ◌ tyᵗ

module _ where -- §-Type-𝕋Λ-Example where
  e1 : Type-𝕋Λ
  e1 = con ℕᵗ ◌-⧜

  e2 : Type-𝕋Λ
  e2 = con 𝔹ᵗ ◌-⧜

x = unify (⧜subst (incl e1)) (⧜subst (incl e2))

module _ {A : 𝒰 𝑖} {B : 𝒰 𝑗} where
  myfun : A +-𝒰 B -> Bool
  myfun (left a) = false
  myfun (right b) = true


instance
  tokdef : TokenDefinition (UntypedCon TypeAxiom-𝕋Λ)
  TokenDefinition.all tokdef =
    (_ , _ , 𝔹ᵗ)
    ∷ (_ , _ , ℕᵗ)
    ∷ (_ , _ , ⇒ᵗ)
    ∷ (_ , _ , ▻ᵗ)
    ∷ (_ , _ , []ᵗ)
    ∷ []
  TokenDefinition.name tokdef (_ , _ , ⇒ᵗ) = "Arr"
  TokenDefinition.name tokdef (_ , _ , ℕᵗ) = "Nat"
  TokenDefinition.name tokdef (_ , _ , 𝔹ᵗ) = "Bool"
  TokenDefinition.name tokdef (_ , _ , []ᵗ) = "Nil"
  TokenDefinition.name tokdef (_ , _ , ▻ᵗ) = "Cons"



compareLambdaType : String -> String -> String
compareLambdaType s t with fromString {{fromString:ProductTheory {𝒯 = TypeAxiom-𝕋Λ} {{tokdef}}}} s | fromString {{fromString:ProductTheory {𝒯 = TypeAxiom-𝕋Λ} {{tokdef}}}} t
... | right a | left b = b
... | left a | left b = a <> " & " <> b
... | left a | right _ = a
... | right (_ , xb , x) | right (_ , yb , y) with xb ≟-Str yb
... | yes p = "same sort at least!"
... | no ¬p = "different sorts!"



