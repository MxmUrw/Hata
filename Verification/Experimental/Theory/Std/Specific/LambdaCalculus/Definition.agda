
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
open import Verification.Experimental.Theory.Std.Specific.ProductTheory.Instance.FromString3
open import Verification.Experimental.Theory.Std.Specific.ProductTheory.Instance.hasBoundaries
open import Verification.Experimental.Theory.Std.Specific.ProductTheory.Instance.FormalSystem
open import Verification.Experimental.Theory.Std.Generic.FormalSystem.Definition
open import Verification.Experimental.Category.Std.Limit.Specific.Coproduct.Definition
open import Verification.Experimental.Category.Std.Limit.Specific.Coequalizer.Definition
open import Verification.Experimental.Data.Substitution.Definition


data Sort-𝕋Λ : 𝒰₀ where
  tyᵗ ctxᵗ : Sort-𝕋Λ

private
  lem-2 : (a b : Sort-𝕋Λ) → Decision (a ≡-Str b)
  lem-2 tyᵗ tyᵗ = yes refl-≣
  lem-2 tyᵗ ctxᵗ = no (λ ())
  lem-2 ctxᵗ tyᵗ = no (λ ())
  lem-2 ctxᵗ ctxᵗ = yes refl-≣

instance
  isDiscrete:Sort-𝕋Λ : isDiscrete Sort-𝕋Λ
  isDiscrete:Sort-𝕋Λ = record { _≟-Str_ = lem-2 }

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
isDiscrete:Sort TypeAxiom-𝕋Λ = it
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

instance
  IShow:Sort-𝕋Λ : IShow (Sort-𝕋Λ)
  IShow.show IShow:Sort-𝕋Λ tyᵗ = "Ty"
  IShow.show IShow:Sort-𝕋Λ ctxᵗ = "Ctx"


𝑹' = 𝑹 {𝒯 =  TypeAxiom-𝕋Λ}

dounify : 𝑹' -> 𝑹' -> String +-𝒰 𝑹'
dounify (τsx , τx , x) (τsy , τy , y) with τx ≟-Str τy
... | no _ = left "Wrong result kinds!"
... | yes refl-≣ = case unify fx' fy' of (λ x₁ → left "Could not unify!") λ _ → right (getArr (fx' ◆ π₌))
  where
      -- xa : ⧜𝐒𝐮𝐛𝐬𝐭 ′(Term-𝕋× TypeAxiom-𝕋Λ)′
      asx : 𝐂𝐭𝐱 (TypeAxiom-𝕋Λ)
      asx = incl τsx
      ax : 𝐂𝐭𝐱 (TypeAxiom-𝕋Λ)
      ax = incl (incl τx)
      fx : ax ⟶ asx
      fx = ⧜subst (incl x)

      asy : 𝐂𝐭𝐱 (TypeAxiom-𝕋Λ)
      asy = incl τsy
      ay : 𝐂𝐭𝐱 (TypeAxiom-𝕋Λ)
      ay = incl (incl τy)
      fy : ay ⟶ asy
      fy = ⧜subst (incl y)

      fx' : ax ⟶ asx ⊔ asy
      fx' = fx ◆ ι₀

      fy' : ay ⟶ asx ⊔ asy
      fy' = fy ◆ ι₁

      getArr : ∀{b} -> ax ⟶ b -> 𝑹'
      getArr (⧜subst (incl f)) = _ , (_ , f)


compareLambdaType : String -> String
compareLambdaType s with ProductTheory:fromString {𝒯 = TypeAxiom-𝕋Λ} s
... | left err = "Error " <> err
... | just ((_ , _ , x) , (_ , _ , y)) = "Got types: " <> show x <> " and " <> show y
                                         <> "\nthe unification is: " <> case res of (λ x -> x) (λ (_ , _ , a) -> show a)
      where
        res = dounify (_ , _ , x) (_ , _ , y)



