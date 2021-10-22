
module Verification.Experimental.Category.Std.Monad.KleisliCategory.Instance.Monoidal where

open import Verification.Conventions

open import Verification.Experimental.Set.Setoid
open import Verification.Experimental.Set.Discrete
open import Verification.Experimental.Data.Product.Definition
open import Verification.Experimental.Category.Std.Category.Definition
open import Verification.Experimental.Category.Std.Category.Construction.Product
open import Verification.Experimental.Category.Std.Functor.Definition
open import Verification.Experimental.Category.Std.Functor.Instance.Category
open import Verification.Experimental.Category.Std.Natural.Definition
open import Verification.Experimental.Category.Std.Category.Instance.Category
open import Verification.Experimental.Category.Std.Monad.Definition
open import Verification.Experimental.Category.Std.Monad.KleisliCategory.Definition
open import Verification.Experimental.Category.Std.Morphism.Iso
open import Verification.Experimental.Algebra.Monoid.Definition

open import Verification.Experimental.Category.Std.Category.Structured.Monoidal.Definition


module _ {𝒞 : Category 𝑖} {{_ : isMonoidal 𝒞}}
         {𝒟 : Category 𝑗} {{_ : isMonoidal 𝒟}} where

-- module _ {𝒞 : MonoidalCategory 𝑖}
--          {𝒟 : MonoidalCategory 𝑗} where

  record isLaxMonoidalFunctor (F : Functor 𝒞 𝒟) : 𝒰 (𝑖 ､ 𝑗) where
    field lax-unit : ◌ ⟶ ⟨ F ⟩ ◌
    field lax-mult : ∀{a b} -> ⟨ F ⟩ a ⋆ ⟨ F ⟩ b ⟶ ⟨ F ⟩ (a ⋆ b)
    -- field lax-unit-l : ∀{a} -> Eq (◌ ⋆ ⟨ F ⟩ a ⟶ ⟨ F ⟩ a)
    --                               ((lax-unit ⇃⊗⇂ id) ◆ lax-mult ◆ map ⟨ unit-l-⋆ ⟩)
    --                               ⟨ unit-l-⋆ ⟩

    -- field lax-unit-l : ∀{a} -> Eq (◌ ⋆ ⟨ F ⟩ a ⟶ ⟨ F ⟩ a)
    --                               ((lax-unit ⇃⊗⇂ id) ◆ lax-mult ◆ map ⟨ unit-l-⋆ ⟩)
    --                               ⟨ unit-l-⋆ ⟩

  open isLaxMonoidalFunctor {{...}} public


module _ {𝒞 : Category 𝑖} {{_ : isMonoidal 𝒞}} where

  record isMonoidalMonad (T : Monad 𝒞) : 𝒰 𝑖 where
    field {{isLaxMonoidalFunctor:this}} : isLaxMonoidalFunctor ′ ⟨ T ⟩ ′
    field compat-lax-unit : lax-unit ∼ pure _
    -- field compat-lax-mult : ∀{a b} -> Eq (a ⋆ b ⟶ ⟨ T ⟩ (a ⋆ b))
    --                                      (pure ⇃⊗⇂ pure ◆ lax-mult)
    --                                      pure

  open isMonoidalMonad {{...}} public

module _ {𝒞 : Category 𝑖} {{_ : isMonoidal 𝒞}}
         {T : Monad 𝒞} {{_ : isMonoidalMonad T}}
         where

  infixl 70 _⊗-𝐊𝐥𝐬_ _⇃⊗⇂-𝐊𝐥𝐬_
  _⊗-𝐊𝐥𝐬_ : (a b : 𝐊𝐥𝐬 T) -> 𝐊𝐥𝐬 T
  _⊗-𝐊𝐥𝐬_ a b = incl (⟨ a ⟩ ⋆ ⟨ b ⟩)

  𝖨𝖽-𝐊𝐥𝐬 : 𝐊𝐥𝐬 T
  𝖨𝖽-𝐊𝐥𝐬 = incl ◌

  private
    instance
      _ : isSetoid (𝐊𝐥𝐬 T)
      _ = isSetoid:byCategory

  _⇃⊗⇂-𝐊𝐥𝐬_ : ∀{a b c d : 𝐊𝐥𝐬 T} -> (f : a ⟶ b) (g : c ⟶ d) -> (a ⊗-𝐊𝐥𝐬 c ⟶ b ⊗-𝐊𝐥𝐬 d)
  _⇃⊗⇂-𝐊𝐥𝐬_ f g = incl ((⟨ f ⟩ ⇃⊗⇂ ⟨ g ⟩) ◆ lax-mult)

  private
    lem-10 : ∀{a b : 𝐊𝐥𝐬 T} -> (id {a = a} ⇃⊗⇂-𝐊𝐥𝐬 id {a = b}) ∼ id
    lem-10 = incl {!!} -- compat-lax-mult


  isFunctor:⊗-𝐊𝐥𝐬 : isFunctor (𝐊𝐥𝐬 T ×-𝐂𝐚𝐭 𝐊𝐥𝐬 T) (𝐊𝐥𝐬 T) (λ₋ _⊗-𝐊𝐥𝐬_)
  isFunctor.map isFunctor:⊗-𝐊𝐥𝐬              = λ₋ _⇃⊗⇂-𝐊𝐥𝐬_
  isFunctor.isSetoidHom:map isFunctor:⊗-𝐊𝐥𝐬  = {!!} -- record { cong-∼ = λ (p , q) → incl (cong-∼ (⟨ p ⟩ , ⟨ q ⟩) ◈ refl) }
  isFunctor.functoriality-id isFunctor:⊗-𝐊𝐥𝐬 = lem-10
  isFunctor.functoriality-◆ isFunctor:⊗-𝐊𝐥𝐬  = {!!}


  private
    lem-1 : {a : Kleisli T} → (𝖨𝖽-𝐊𝐥𝐬 ⊗-𝐊𝐥𝐬 a) ∼ a
    lem-1 = cong-≅ unit-l-⋆


  instance
    isMonoid:Kleisli : isMonoid (Kleisli T since isSetoid:byCategory)
    isMonoid:Kleisli = record
                         { _⋆_        = _⊗-𝐊𝐥𝐬_
                         ; ◌          = 𝖨𝖽-𝐊𝐥𝐬
                         ; unit-l-⋆   = lem-1
                         ; unit-r-⋆   = cong-≅ unit-r-⋆
                         ; assoc-l-⋆  = cong-≅ assoc-l-⋆
                         ; _`cong-⋆`_ = λ p q -> cong-≅ {{isFunctor:⊗-𝐊𝐥𝐬}} (into-×-≅ p q)
                         }

  instance
    isMonoidal:Kleisli : isMonoidal (𝐊𝐥𝐬 T)
    isMonoidal.isMonoid:this isMonoidal:Kleisli    = isMonoid:Kleisli
    isMonoidal.isFunctor:⋆ isMonoidal:Kleisli       = isFunctor:⊗-𝐊𝐥𝐬
    isMonoidal.compat-Monoidal-⋆ isMonoidal:Kleisli = {!!} -- λ p q → refl


