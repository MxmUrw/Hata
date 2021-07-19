
module Verification.Experimental.Data.Universe.Instance.Monoidal where

open import Verification.Conventions

open import Verification.Experimental.Set.Setoid.Definition
open import Verification.Experimental.Data.Universe.Definition
open import Verification.Experimental.Category.Std.Morphism.Iso
open import Verification.Experimental.Category.Std.Category.Definition
open import Verification.Experimental.Category.Std.Category.Construction.Product
open import Verification.Experimental.Category.Std.Functor.Definition
open import Verification.Experimental.Category.Std.Category.Structured.Monoidal.Definition
open import Verification.Experimental.Algebra.Monoid.Definition
open import Verification.Experimental.Data.Universe.Instance.Category
open import Verification.Experimental.Category.Std.Natural.Iso

private

  instance
    _ : isSetoid (𝐔𝐧𝐢𝐯 𝑖)
    _ = isSetoid:byCategory

  infixr 40 _×_
  _×_ : 𝒰 𝑖 -> 𝒰 𝑖 -> 𝒰 𝑖
  _×_ A B = A ×-𝒰 B

  lem-1 : ∀{A : 𝒰 𝑖} -> ⊤-𝒰 × A ≅ A
  lem-1 {A = A} = snd since P
    where
      P : isIso (hom snd)
      P = record
          { inverse-◆ = λ a -> (tt , a)
          ; inv-r-◆ = λ {i (tt , a) -> tt , a}
          ; inv-l-◆ = refl
          }

  lem-2 : ∀{A : 𝒰 𝑖} -> A × ⊤-𝒰 ≅ A
  lem-2 {A = A} = fst since P
    where
      P : isIso (hom fst)
      P = record
          { inverse-◆ = λ a -> (a , tt)
          ; inv-r-◆ = λ {i (a , tt) -> a , tt}
          ; inv-l-◆ = refl
          }

  lem-3 : ∀{A B C : 𝒰 𝑖} -> (A × B) × C ≅ A × (B × C)
  lem-3 {A = A} {B} {C} = f since P
    where
      f : (A × B) × C -> A × (B × C)
      f ((a , b) , c) = a , (b , c)

      g : A × (B × C) -> (A × B) × C
      g (a , (b , c)) = ((a , b) , c)

      P : isIso (hom f)
      P = record
          { inverse-◆ = g
          ; inv-r-◆ = λ {i ((a , b) , c) -> ((a , b) , c)}
          ; inv-l-◆ = λ {i (a , (b , c)) -> (a , (b , c))}
          }

instance
  isFunctor:×-𝒰 : isFunctor ′(𝐔𝐧𝐢𝐯 𝑖 × 𝐔𝐧𝐢𝐯 𝑖)′ (𝐔𝐧𝐢𝐯 𝑖) (λ₋ _×_)
  isFunctor.map isFunctor:×-𝒰 = λ (f , g) -> λ (a , b) -> (f a , g b)
  isFunctor.isSetoidHom:map isFunctor:×-𝒰 = record { cong-∼ = λ p i (a , b) → p .fst i a , p .snd i b }
  isFunctor.functoriality-id isFunctor:×-𝒰 = refl
  isFunctor.functoriality-◆ isFunctor:×-𝒰 = refl

instance
  isMonoid:𝐔𝐧𝐢𝐯 : isMonoid (𝐔𝐧𝐢𝐯 𝑖)
  isMonoid:𝐔𝐧𝐢𝐯 = record
                  { _⋆_        = _×_
                  ; ◌          = ⊤-𝒰
                  ; unit-l-⋆   = lem-1
                  ; unit-r-⋆   = lem-2
                  ; assoc-l-⋆  = lem-3
                  ; assoc-r-⋆  = lem-3 ⁻¹
                  ; _`cong-⋆`_ = λ p q -> cong-≅ (into-×-≅ p q)
                  }

instance
  isMonoidal:𝐔𝐧𝐢𝐯 : isMonoidal (𝐓𝐲𝐩𝐞 𝑖)
  isMonoidal.isMonoid:this isMonoidal:𝐔𝐧𝐢𝐯 = it
  isMonoidal.isFunctor:⋆ isMonoidal:𝐔𝐧𝐢𝐯 = it
  isMonoidal.isNaturalIso:unit-l-⋆ isMonoidal:𝐔𝐧𝐢𝐯 = naturalIso (λ f → refl) (λ f → refl)
  isMonoidal.isNaturalIso:unit-r-⋆ isMonoidal:𝐔𝐧𝐢𝐯 = naturalIso (λ f -> refl) (λ f -> refl)
  isMonoidal.compat-Monoidal-⋆ isMonoidal:𝐔𝐧𝐢𝐯 = λ _ _ -> refl
  isMonoidal.isNaturalIso:assoc-l-⋆ isMonoidal:𝐔𝐧𝐢𝐯 = naturalIso (λ f -> refl) (λ f -> refl)
  isMonoidal.triangle-Monoidal isMonoidal:𝐔𝐧𝐢𝐯 = incl refl
  isMonoidal.pentagon-Monoidal isMonoidal:𝐔𝐧𝐢𝐯 = incl refl



