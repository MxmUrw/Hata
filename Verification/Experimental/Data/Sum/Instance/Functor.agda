
module Verification.Experimental.Data.Sum.Instance.Functor where

open import Verification.Conventions
open import Verification.Experimental.Set.Function.Injective
open import Verification.Experimental.Set.Setoid
open import Verification.Experimental.Data.Sum.Definition
open import Verification.Experimental.Category.Std.Category.Definition
open import Verification.Experimental.Category.Std.Functor.Definition
open import Verification.Experimental.Category.Std.Functor.Instance.Category
open import Verification.Experimental.Data.Universe.Everything


-- | Fix a type [..].
module _ {A : 𝒰 𝑖} where

  -- | Then |_+_| is a functor...
  instance
    isFunctor:+₁ : isFunctor (𝐓𝐲𝐩𝐞 𝑗) (𝐓𝐲𝐩𝐞 _) (A +-𝒰_)
    isFunctor:+₁ = functor F {{isSetoidHom:F}} lem-1 lem-2

      where
        F : {X Y : 𝒰 _} -> (X ⟶ Y) -> (A +-𝒰 X) ⟶ (A +-𝒰 Y)
        F f = incl (either left (right ∘ ⟨ f ⟩))

        instance
          isSetoidHom:F : ∀{X Y} -> isSetoidHom _ _ (F {X} {Y})
          isSetoidHom:F = record
            {preserves-∼ = λ {(incl p) → incl (λ i -> either left (right ∘ p i))}
            }

        lem-1 : ∀{a} → F (incl (id-𝒰 {A = a})) ∼ incl (id-𝒰)
        lem-1 = incl (λ { i (left x) -> left x
                        ; i (right x) -> right x})

        lem-2 : {a b c : 𝒰' _} {f : Hom a b} {g : Hom b c} →
                F (incl (⟨ f ⟩ ◆-𝒰 ⟨ g ⟩)) ∼ incl (⟨ F f ⟩ ◆-𝒰 ⟨ F g ⟩)
        ⟨ lem-2 ⟩ = funExt $ λ
                      { (left x)  -> refl
                      ; (right x) -> refl
                      }

instance
  isFunctor:+ : isFunctor (𝐓𝐲𝐩𝐞 𝑖) (𝐅𝐮𝐧𝐜 (𝐓𝐲𝐩𝐞 𝑗) (𝐓𝐲𝐩𝐞 _)) (λ A -> A +⧿)
  isFunctor:+ = functor {!!} {{{!!}}} {!!} {!!}





