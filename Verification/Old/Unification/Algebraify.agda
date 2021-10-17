{-# OPTIONS --rewriting #-}

module Verification.Unification.Algebraify where

open import Verification.Conventions
open import Verification.Core.Type
open import Verification.Core.Algebra
open import Verification.Core.Order
open import Verification.Core.Category.Definition
open import Verification.Core.Category.Monad
open import Verification.Core.Category.Quiver
open import Verification.Core.Category.FreeCategory
open import Verification.Core.Category.Functor
open import Verification.Core.Category.Instance.Type
open import Verification.Core.Category.Instance.SmallCategories
open import Verification.Core.Category.Instance.TypeProperties
open import Verification.Core.Category.Instance.Set
open import Verification.Core.Category.KanLimit.Definition
open import Verification.Core.Category.Monad
open import Verification.Unification.RecAccessible
open import Verification.Core.Homotopy.Level


{-# BUILTIN REWRITE _≡_ #-}

--------------------------------------------------------------------
-- == The functor to Recursion Modules
-- | Let A, B, C be sets, and let $T$ be a fixed \AD{RecMonad} in this section.

-- Monoid:Path : Quiver 𝑖 -> Monoid (𝑖 ⌄ 0 ⊔ 𝑖 ⌄ 1)
-- ⟨ Monoid:Path Q ⟩ = Maybe (∑ λ (x : ⟨ Q ⟩) -> ∑ λ (y : ⟨ Q ⟩) -> Edge {{of Q}} x y)
-- IMonoid.𝟷 (of Monoid:Path Q) = {!!}
-- IMonoid._⋅_ (of Monoid:Path Q) = {!!}
-- IMonoid.assoc-⋅ (of Monoid:Path Q) = {!!}
-- IMonoid.unit-l-⋅ (of Monoid:Path Q) = {!!}
-- IMonoid.unit-r-⋅ (of Monoid:Path Q) = {!!}

mirror : ∀{𝒞 : Category 𝑖} {𝒟 : Category 𝑗} -> Functor 𝒞 (𝒟 ᵒᵖ) -> Functor (𝒞 ᵒᵖ) 𝒟
⟨ mirror F ⟩ = ⟨ F ⟩
IFunctor.map (of mirror F) = map
IFunctor.functoriality-id (of mirror F) = functoriality-id
IFunctor.functoriality-◆ (of mirror F) = functoriality-◆
IFunctor.functoriality-≣ (of mirror F) = functoriality-≣

byFirstP : ∀{A : 𝒰 𝑖} {B : A -> 𝒰 𝑗} {{_ : ∀{a : A} -> IHType 1 (B a)}}
           -> {a1 a2 : A} {b1 : B a1} {b2 : B a2} -> (p : a1 ≡ a2)
           -> PathP (λ i -> ∑ λ (a : A) -> B a) (a1 , b1) (a2 , b2)
byFirstP = {!!}


PSh : (𝒞 : Category 𝑖) -> ∀ 𝑗 -> 𝒰 _
PSh 𝒞 𝑗 = Functor (𝒞 ᵒᵖ) `(Set 𝑗)`


module _ {K : 𝒰 𝑖} (T : Functor `(IdxSet K 𝑖)` `(IdxSet K 𝑖)`) {{_ : IMonad T}} {{_ : IRecAccessible-Monad T}} where
  private
    Q : Quiver (𝑖 , 𝑖 , 𝑖)
    ⟨ Q ⟩ = K
    IQuiver.Edge (of Q) a b = Maybe (Edge {{Dir}} b a)
    IQuiver._≈_ (of Q) = _≡_
    IQuiver.IEquivInst (of Q) = IEquiv:Path

  𝔇 = (Category:Free Q)

  instance _ = of 𝔇
  instance _ = of Q

  Mod : IdxSet K 𝑖 -> K -> Set 𝑖
  ⟨ Mod X k ⟩ = ∑ λ j -> Hom {{of 𝔇}} k j ×-𝒰 (𝟚-𝒰 +-𝒰 (⟨ ⟨ T ⟩ X ⟩ j))
  of Mod X k = {!!}

  private
    data isNormal {A : IdxSet K 𝑖} {k} : ⟨ Mod A k ⟩ -> 𝒰 (𝑖) where
      anything : ∀{a : ⟨ Mod A k ⟩} -> isNormal a
        -- by-[] : ∀{a : ⟨ T ⟩ A} -> (depth a ≡ 0 -> 𝟘-𝒰) -> isNormal ([] , a)
        -- by-depth : ∀{ds} -> ∀{a : ⟨ T ⟩ A} -> depth a ≡ 0 -> isNormal (ds , a)

    instance
      IProp:isNormal : ∀{A : IdxSet K 𝑖} {k} {a : ⟨ Mod A k ⟩} -> IHType 1 (isNormal a)
      IProp:isNormal = {!!}

  Mod-Normal : IdxSet K 𝑖 -> K -> Set 𝑖
  ⟨ Mod-Normal X k ⟩ = ∑ λ (a : ⟨ Mod X k ⟩) -> isNormal a
  of Mod-Normal X k = {!!}

  -- syntax ⟨_⟩ (⟨_⟩ a) = ⟨⟨_⟩⟩ a

  private
    module _ {X : IdxSet K 𝑖} where

      ν-impl-1 : {j : K} {k : K} -> (p : Edge {{of Q}} k j) -> ⟨ ⟨ T ⟩ X ⟩ j -> Maybe (𝟚-𝒰 +-𝒰 (⟨ ⟨ T ⟩ X ⟩ k))
      ν-impl-1 nothing x = just (left ₀)
      ν-impl-1 (just e) x with ⟨ ⟨ decompose ⟩ ⟩ _ x
      ... | left _ = nothing
      ... | just xs = just (xs _ e)
--       ... | left x₂ = j , some (last e) , right x
--       ... | just xs = let x = xs _ e
                      -- in ?

      ν-impl-2 : {j : K} {k : K} -> (p : QPath {{of Q}} k j) -> ⟨ ⟨ T ⟩ X ⟩ j -> ⟨ Mod X k ⟩
      ν-impl-2 (last e) x with ν-impl-1 e x
      ... | nothing = (_ , some (last e) , right x)
      ... | just x' = _ , id , x'
      ν-impl-2 (e ∷ es) x with ν-impl-1 e x
      ... | nothing = _ , some (e ∷ es) , right x
      ... | just (left x') = _ , id , left x'
      ... | just (just x') = ν-impl-2 _ es x'

      ν : ∀{k} -> ⟨ Mod X k ⟩ -> ⟨ Mod X k ⟩
      ν (j , p , left x) = (_ , id , left x)
      ν (j , id-Q , just x) = (j , id-Q , just x)
      ν (j , some p , just x) = ν-impl-2 j p x

      isNormal-ν : ∀{k} -> ∀(x : ⟨ Mod X k ⟩) -> isNormal (ν x)
      isNormal-ν x = anything

      ν₁ : ∀{k} -> ⟨ Mod X k ⟩ -> ⟨ Mod-Normal X k ⟩
      ν₁ x = ν x , isNormal-ν x

      idempotent-ν : ∀{k} -> ∀{x : ⟨ Mod X k ⟩} -> ν (ν x) ≡ ν x
      idempotent-ν = {!!}
      -- {-# REWRITE idempotent-ν #-}
      -- ν : ∀{X : IdxSet K 𝑖} {k} -> ⟨ Mod X k ⟩ -> ⟨ Mod-Normal X k ⟩
      -- ν (j , p , left x) = (_ , id , left x) , {!!}
      -- ν (j , id-Q , just x) = (j , id-Q , just x) , {!!}
      -- ν (j , some (last x₁) , just x) = {!!}
      -- ν (j , some (x₁ ∷ ds) , just x) = {!!}

      write : ∀{k j} -> (e : Edge {{of Q}} k j) -> ⟨ Mod X k ⟩ -> ⟨ Mod X j ⟩
      write e (_ , p , x) = (_ , ` e ` ◆ p , x)

      write-comm-impl-2 : {j k l : K} -> (e : Edge {{of Q}} k l) -> (p : QPath {{of Q}} j k) -> (x : ⟨ ⟨ T ⟩ X ⟩ j) -> ν (write e (ν-impl-2 j p x)) ≡ ν-impl-2 j (comp-QPath p (last e)) x
      write-comm-impl-2 e' (last e) x with (ν-impl-1 _ e x)
      ... | just X = {!!}
      ... | left x₁ = {!!}
      -- with split-+ (ν-impl-1 _ e x)
      -- ... | left x₂ = {!!}
      -- ... | just x₂ = {!!}
      write-comm-impl-2 e' (e ∷ p) x = {!!}

      write-comm : ∀{k j} -> (e : Edge {{of Q}} k j) -> (x : ⟨ Mod X k ⟩)-> ν (write e (ν x)) ≡ ν (write e x)
      write-comm e (j , p , left x) = refl
      write-comm e (j , id-Q , just x) = refl
      write-comm e (j , some p , just x) = write-comm-impl-2 e p x

    module _ {X Y : IdxSet K 𝑖} where
      apply : ∀{k} -> (f : X ⟶ ⟨ T ⟩ Y) -> ⟨ Mod X k ⟩ -> ⟨ Mod Y k ⟩
      apply f (_ , p , left x) = (_ , p , left x)
      apply f (_ , p , right x) = (_ , p , right (⟨ f =<< ⟩ _ x))

      apply-comm : ∀{k} -> (f : X ⟶ ⟨ T ⟩ Y) -> (x : ⟨ Mod X k ⟩) -> ν (apply f (ν x)) ≡ ν (apply f x)
      apply-comm f x = {!!}
      -- (_ , p , x) = (_ , ` e ` ◆ p , x)

  𝑺 : IdxSet K 𝑖 -> PSh 𝔇 𝑖
  𝑺 X = free-Diagram f
    where f : QuiverHom (Q) (ForgetCategory ` Set 𝑖 `)
          ⟨ f ⟩ k = Mod-Normal X k
          ⟨ IQuiverHom.qmap (of f) e ⟩ (x , _) = ν₁ (write e x)
          of IQuiverHom.qmap (of f) e = record {}

  private
    module _ {X Y : IdxSet K 𝑖} (f : X ⟶ ⟨ T ⟩ Y) where
      g' : ∀{k} -> ⟨ Mod X k ⟩ -> ⟨ Mod Y k ⟩
      g' ((j , p , left a)) = ((j , p , left a)) -- normaliz
      g' ((j , p , just x)) = (j , p , just (⟨ f =<< ⟩ j x))

      g : ∀(k : K) -> ⟨ 𝑺 X ⟩ k ⟶ ⟨ 𝑺 Y ⟩ k
      ⟨ g k ⟩ (x , xp) = ν₁ (apply f x)

      -- ⟨ g k ⟩ ((j , p , left a) , _) = ν ((j , p , left a)) -- ν (j , p , {!!}) -- (j , p ,  ⟨ f =<< ⟩ j x)
      -- ⟨ g k ⟩ ((j , p , just x) , _) = ν (j , p , just (⟨ f =<< ⟩ j x)) -- (j , p ,  ⟨ f =<< ⟩ j x)
      of g k = record {}

      gp : {a b : K} (e : Maybe (Edge {{Dir}} a b)) (x : ⟨ ⟨ 𝑺 X ⟩ a ⟩) →
            ⟨ map {{of 𝑺 Y}} (⩚ e) ⟩ (⟨ g a ⟩ x) ≡
            ⟨ g b ⟩ (⟨ map {{of 𝑺 X}} (⩚ e) ⟩ x)
      gp e ((j , p , left x) , _) = byFirstP refl
      gp e ((j , p , just x) , pp) = byFirstP P

       where P : ν (write e (ν (apply f (j , p , just x))))
                  ≡
                ν (apply f (ν (write e (j , p , just x))))
             P = write-comm e (apply f (j , p , just x)) ∙ apply-comm f (write e (j , p , just x)) ⁻¹

       -- where P : ν (write e ((ν (j , p , just (⟨ f =<< ⟩ j x)))))
       --            ≡
       --          ν (apply f ((ν ((j , ` e ` ◆ p , just x)))))
       --       P = {!!}

       -- where P : ν
       --          (fst (fst (ν (j , p , just (⟨ f =<< ⟩ j x)))) ,
       --          ` e ` ◆
       --          (fst (snd (fst (ν (j , p , just (⟨ f =<< ⟩ j x))))))
       --          , snd (snd (fst (ν (j , p , just (⟨ f =<< ⟩ j x))))))
       --          ≡
       --          ν (g' (fst (ν ((j , ` e ` ◆ p , just x)))))
       --       P = {!!}



        -- where P : ν
        --         (fst (fst (ν (j , p , just (⟨ f =<< ⟩ j x)))) ,
        --         ` e ` ◆
        --         (fst (snd (fst (ν (j , p , just (⟨ f =<< ⟩ j x))))))
        --         , snd (snd (fst (ν (j , p , just (⟨ f =<< ⟩ j x))))))
        --         ≡
        --         ((ν (g' (j , ` e ` ◆ p , just x))))
        --       P = {!!}

  module _ {X Y : IdxSet K 𝑖} where
    map-𝑺 : (f : X ⟶ ⟨ T ⟩ Y) -> 𝑺 X ⟶ 𝑺 Y
    map-𝑺 f = free-Diagram-Natimpl (g f) (λ e x -> gp f e x)

      -- where g : ∀(k : K) -> ⟨ 𝑺 X ⟩ k ⟶ ⟨ 𝑺 Y ⟩ k
      --       ⟨ g k ⟩ ((j , p , left a) , _) = ν ((j , p , left a)) -- ν (j , p , {!!}) -- (j , p ,  ⟨ f =<< ⟩ j x)
      --       ⟨ g k ⟩ ((j , p , just x) , _) = ν (j , p , just (⟨ f =<< ⟩ j x)) -- (j , p ,  ⟨ f =<< ⟩ j x)
      --       of g k = record {}

      --       gp : {a b : K} (e : Maybe (Edge {{Dir}} a b)) (x : ⟨ ⟨ 𝑺 X ⟩ a ⟩) →
      --             ⟨ map {{of 𝑺 Y}} (⩚ e) ⟩ (⟨ g a ⟩ x) ≡
      --             ⟨ g b ⟩ (⟨ map {{of 𝑺 X}} (⩚ e) ⟩ x)
      --       gp e ((j , p , left x) , _) = {!!}
      --       gp e ((j , p , just x) , _) = {!!}


            -- gp2 : {a b : K}
            --         (e : 𝟙-𝒰 +-𝒰 Edge {{Dir}} a b)
            --         (x
            --         : Σ (Σ K (λ j → Σ (Hom {{of 𝔇 ᵒᵖ}} j a) (λ a₁ → 𝟙-𝒰 +-𝒰 ⟨ ⟨ T ⟩ X ⟩ j)))
            --           (isNormal X a)) →
            --         ν
            --         (fst (fst (⟨ g a ⟩ x)) ,
            --         (some (last e)) ◆ (fst (snd (fst (⟨ g a ⟩ x)))) ,
            --         snd (snd (fst (⟨ g a ⟩ x))))
            --         ≡
            --         ⟨ g b ⟩
            --         (ν
            --         (fst (fst x) ,
            --           (some (last e)) ◆ (fst (snd (fst x)))  ,
            --           snd (snd (fst x))))
            -- gp2 = {!!}
    -- ⟨ ⟨ map-𝑺 f ⟩ {x = k} ⟩ ((j , p , x) , _) = ν (j , p ,  ⟨ f =<< ⟩ j x)
    -- of ⟨ map-𝑺 f ⟩ = record {}
    -- INatural.naturality (of map-𝑺 f) = {!!}


  -- Functor:𝑺 : Functor `(Kleisli ` T `)` `(PSh 𝔇 𝑖)`
  -- ⟨ Functor:𝑺 ⟩ = 𝑺
  -- IFunctor.map (of Functor:𝑺) = map-𝑺
  -- IFunctor.functoriality-id (of Functor:𝑺) = {!!}
  -- IFunctor.functoriality-◆ (of Functor:𝑺) = {!!}
  -- IFunctor.functoriality-≣ (of Functor:𝑺) = {!!}


{-
  𝔇 = Monoid:Free Dir

  private
    Mon : ∀(A : 𝒰 𝑖) -> MonoidModule 𝔇 𝑖
    Mon A = MonoidModule:Free 𝔇 (⟨ T ⟩ A)

  norm' : ⟨ 𝔇 ⟩ -> ⟨ T ⟩ A -> ⟨ Mon A ⟩
  norm' [] a = ([] , a)
  norm' (d ∷ ds) a with ⟨ decompose ⟩ a
  ... | left x = (d ∷ ds , a)
  ... | just x = norm' ds (x d)

  norm : ⟨ Mon A ⟩ -> ⟨ Mon A ⟩
  norm (ds , a) = norm' ds a



  private
    data isNormal : ⟨ Mon A ⟩ -> 𝒰 (𝑖 ⁺) where
       by-[] : ∀{a : ⟨ T ⟩ A} -> (depth a ≡ 0 -> 𝟘-𝒰) -> isNormal ([] , a)
       by-depth : ∀{ds} -> ∀{a : ⟨ T ⟩ A} -> depth a ≡ 0 -> isNormal (ds , a)

    lem::1 : ∀(a : ⟨ Mon A ⟩) -> isNormal a -> norm a ≡ a
    lem::1 ([] , a) P = refl
    lem::1 (d ∷ ds , a) (by-depth P) with ⟨ decompose ⟩ a | strict a
    ... | left a₂ | X = refl
    ... | just a₂ | X =
      let P₂ : depth (a₂ d) < depth a
          P₂ = X d

          P₃ : depth (a₂ d) < 0
          P₃ = transport (λ i -> depth (a₂ d) < P i) P₂

          P₄ : 𝟘-𝒰
          P₄ = P₃ .snd (≤0→≡0 (P₃ .fst))

      in 𝟘-elim P₄

    lem::2 : ∀(ds : ⟨ 𝔇 ⟩) -> (a : ⟨ T ⟩ A) -> isNormal (norm' ds a)
    lem::2 [] a with split-ℕ (depth a)
    ... | left x = by-depth x
    ... | just x = by-[] (λ a≡0 -> zero≢suc (a≡0 ⁻¹ ∙ snd x))
    lem::2 (d ∷ ds) a with ⟨ decompose ⟩ a | strict a
    ... | left x | P = by-depth (transport (λ i -> depth (P (~ i)) ≡ 0) depth/return)
    ... | just x | P = lem::2 ds (x d)

    lem::3 : ∀(a : ⟨ Mon A ⟩) -> norm (norm a) ≡ norm a
    lem::3 a = lem::1 (norm a) (lem::2 (fst a) (snd a))

  -}





