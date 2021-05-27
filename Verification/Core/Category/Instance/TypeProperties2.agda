
{-# OPTIONS --cubical --allow-unsolved-metas #-}

module Verification.Core.Category.Instance.TypeProperties2 where

open import Verification.Conventions
open import Verification.Core.Category.Definition
open import Verification.Core.Category.Functor
open import Verification.Core.Category.Adjunction
open import Verification.Core.Category.KanLimit.Definition2
-- open import Verification.Core.Category.Limit.Definition
-- open import Verification.Core.Category.Limit.Product
-- open import Verification.Core.Category.Limit.Equalizer
-- open import Verification.Core.Category.Monad
open import Verification.Core.Category.Instance.Type
open import Verification.Core.Category.Instance.Cat
open import Verification.Core.Category.FreeCategory
open import Verification.Core.Category.Quiver


--------------------------------------------------------------------
-- Products

module _ where
  private
    L : Functor (⩚ (`𝟚` ⟶ ⩚ 𝒰 𝑖 )) (⩚ (𝟙 ⟶ ⩚ 𝒰 𝑖)) --Fun[ ⩚ 𝟙 , ⩚ 𝒰 𝑖 ]
    ⟨ L ⟩ z = free-Diagram-Lift d
      where d : QuiverHom (⩚ ⊤) (ForgetCategory (⩚ 𝒰 _))
            ⟨ d ⟩ _ = ⟨ z ⟩ (↥ ₀) ×-𝒰 ⟨ z ⟩ (↥ ₁)
            -- QuiverHom.qmap d ()
    IFunctor.map (of L) α = free-Diagram-Nat f fp
      where f = λ {_ (x , y) -> ⟨ α ⟩ x , ⟨ α ⟩ y}
            fp = λ {()}
    IFunctor.functoriality-id (of L) x = refl
    IFunctor.functoriality-◆ (of L) x = refl
    IFunctor.functoriality-≣ (of L) p x i (a , b) = (p (↥ ₀) i a , p (↥ ₁) i b)

    lem::1 : (! `𝟚` *) ⊣ L {𝑖 = 𝑖}
    ⟨ IAdjoint.embed lem::1 ⟩ = free-Diagram-Nat f fp
      where f = λ _ a -> (a , a)
            fp = λ {()}
    INatural.naturality (of IAdjoint.embed lem::1) α x = refl
    ⟨ IAdjoint.eval lem::1 ⟩ = free-Diagram-Nat f (λ {()})
      where f = λ { ₀ (v , w) -> v
                  ; ₁ (v , w) -> w}
    INatural.naturality (of IAdjoint.eval lem::1) f (↥ ₀) = refl
    INatural.naturality (of IAdjoint.eval lem::1) f (↥ ₁) = refl
    IAdjoint.reduce-Adj-β lem::1 (↥ ₀) = refl
    IAdjoint.reduce-Adj-β lem::1 (↥ ₁) = refl
    IAdjoint.reduce-Adj-η lem::1 _ = refl

  instance
    lem::2 : has(`𝟚`)ShapedLimits (⩚ 𝒰 𝑖)
    fst lem::2 = L
    snd lem::2 = lem::1

--------------------------------------------------------------------
-- Equalizers

data Pair : 𝒰₀ where
  ₀ ₁ : Pair


Quiver:Pair : Quiver (many ℓ₀)
⟨ Quiver:Pair ⟩ = Pair
IQuiver.Edge (of Quiver:Pair) ₀ ₀ = ⊥
IQuiver.Edge (of Quiver:Pair) ₀ ₁ = 𝟚-𝒰
IQuiver.Edge (of Quiver:Pair) ₁ b = ⊥
IQuiver._≈_ (of Quiver:Pair) = _≡_
IQuiver.IEquivInst (of Quiver:Pair) = IEquiv:Path

Category:Pair = Category:Free (Quiver:Pair)

instance
  ICategory:Pair = of Category:Pair

instance
  Index-Notation:Diagram : ∀{S : Quiver (ℓ₀ , ℓ₀ , ℓ₀)} {X : Category 𝑖} -> Index-Notation ((↑ Category:Free S) ⟶ X)
                                                                                           (⟨ S ⟩ ×-𝒰 ⟨ S ⟩)
                                                                                           (IAnything)
                                                                                           (λ (D , (a , b)) -> Edge {{of S}} a b -> Hom (⟨ D ⟩ (lift a)) (⟨ D ⟩ (lift b)))
  (Index-Notation:Diagram Index-Notation.⌄ D) (a , b) e = map (lift (some (last e)))

hom : {C : 𝒰 𝑖} {{_ : ICategory C 𝑗}} -> (a b : C) -> Hom a b -> Hom a b
hom = {!!}

module _ where
  private
    L : Functor (⩚ (↑ Category:Pair ⟶ ⩚ 𝒰 𝑖)) (⩚ (𝟙 ⟶ ⩚ 𝒰 𝑖))
    ⟨ L {𝑖} ⟩ F = free-Diagram-Lift f
      where f : QuiverHom (⩚ ⊤) (ForgetCategory (⩚ 𝒰 _))
            ⟨ f ⟩ _ = ∑ λ (x : ⟨ F ⟩ (↥ ₀)) -> (F ⌄ (₀ , ₁)) ₀ x ≡ (F ⌄ (₀ , ₁)) ₁ x
            IQuiverHom.qmap (of f) e x = x
    IFunctor.map (of L) α = free-Diagram-Nat f (λ {()})
      where f = λ {_ (x , xp) -> ⟨ α ⟩ x , let P : (⟨ α ⟩ ◆ map _) x ≡ (⟨ α ⟩ ◆ map _) x
                                               P = (cong (_$ x) (naturality _)) ∙ cong ⟨ α ⟩ xp ∙ (cong (_$ x) (naturality _ ⁻¹))
                                           in P}
      -- where f = λ {_ (x , xp) -> ⟨ α ⟩ x , let P : ⟨ α ⟩ ◆ map _ ≡ ⟨ α ⟩ ◆ map _
      --                                          P = naturality _ ∙ {!!}
      --                                      in cong (_$ x) P}
    IFunctor.functoriality-id (of L) α = funExt (λ {(x , xp) i -> x , {!!}}) -- ({!!} , {!!})
    IFunctor.functoriality-◆ (of L) = {!!}
    IFunctor.functoriality-≣ (of L) = {!!}

            -- map {{of F}} (hom {{of (↑₀ {𝑗 = (𝑖 ⁺ , 𝑖 , 𝑖)} Category:Pair)}} (lift ₀) (lift ₁) (lift (some ({!!} ∷ {!!})))) {!!} ≡ {!!}
