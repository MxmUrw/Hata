
{-# OPTIONS --rewriting #-}

module Verification.Unification.Target.Presheaves.Functor where

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


-- {-# BUILTIN REWRITE _≡_ #-}

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

mirror-Functor : ∀{𝒞 : Category 𝑖} {𝒟 : Category 𝑗} -> Functor 𝒞 (𝒟 ᵒᵖ) -> Functor (𝒞 ᵒᵖ) 𝒟
⟨ mirror-Functor F ⟩ = ⟨ F ⟩
IFunctor.map (of mirror-Functor F) = map
IFunctor.functoriality-id (of mirror-Functor F) = functoriality-id
IFunctor.functoriality-◆ (of mirror-Functor F) = functoriality-◆
IFunctor.functoriality-≣ (of mirror-Functor F) = functoriality-≣

mirror-Nat : ∀{𝒞 : Category 𝑖} {𝒟 : Category 𝑗} -> {F G : Functor 𝒞 (𝒟 ᵒᵖ)} -> (α : Natural F G) -> Natural (mirror-Functor G) (mirror-Functor F)
⟨ mirror-Nat a ⟩ {x} = ⟨ a ⟩
INatural.naturality (of mirror-Nat a) = λ f -> sym (naturality f)

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
    IQuiver.Edge (of Q) a b = Maybe (Edge {{Dir}} a b)
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
      by-[] : ∀{a : 𝟚-𝒰 +-𝒰 ⟨ ⟨ T ⟩ A ⟩ k} -> isNormal (_ , id-Q , a)
      by-eval : ∀{j} -> ∀{a : ⟨ ⟨ T ⟩ A ⟩ j} -> {a' : ⟨ A ⟩ j} -> ⟨ ⟨ decompose ⟩ ⟩ _ a ≡-Str left a'
                 -> (p : Hom k j) -> isNormal (_ , p , right a)

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

      -- ν-impl-1 : {j : K} {k : K} -> (p : Edge {{of Q}} k j) -> ⟨ ⟨ T ⟩ X ⟩ j -> Maybe (𝟚-𝒰 +-𝒰 (⟨ ⟨ T ⟩ X ⟩ k))
      -- ν-impl-1 nothing x = just (left ₀)
      -- ν-impl-1 (just e) x with ⟨ ⟨ decompose ⟩ ⟩ _ x
      -- ... | left _ = nothing
      -- ... | just xs = just (xs _ e)

      -- ν-impl₁ : {j : K} {k : K} -> (p : QPath {{of Q}} k j) -> 𝟚-𝒰 +-𝒰 ⟨ ⟨ T ⟩ X ⟩ j -> ⟨ Mod-Normal X k ⟩

      ν-impl : {j : K} {k : K} -> (p : QPath {{of Q}} k j) -> 𝟚-𝒰 +-𝒰 ⟨ ⟨ T ⟩ X ⟩ j -> ⟨ Mod X k ⟩
      ν-impl p (left x) = _ , id , left ₀
      ν-impl (last nothing) (right x) = _ , id , left ₀
      ν-impl (last (just e)) (right x) with split-+-Str (⟨ ⟨ decompose ⟩ ⟩ _ x)
      ... | left _        = _ , some (last (just e)) , right x
      ... | just (xs , _) = _ , id , (xs _ e)
      -- ν-impl (nothing ∷ p) (right x) = _ , id , left ₀
      ν-impl (e ∷ p) (right x) with ν-impl p (right x)
      ... | (_ , some p' , x')       = _ , some (e ∷ p') , x'
      ... | (_ , id-Q , left x₁)     = _ , id , left ₀
      ... | (_ , id-Q , just x')     with split-+-Str (⟨ ⟨ decompose ⟩ ⟩ _ x')
      ... | left _         = _ , some (last (e)) , just x' -- restore old x', with last existing edge e
      ν-impl (nothing ∷ p) (just x) | (_ , id-Q , just x')     | just (x'' , _) = _ , id , left ₀
      ν-impl (just e ∷ p) (just x)  | (_ , id-Q , just x')     | just (x'' , _) = _ , id-Q , x'' _ e

      ν-impl-isNormal : {j : K} {k : K} -> (p : QPath {{of Q}} k j) -> (x : 𝟚-𝒰 +-𝒰 ⟨ ⟨ T ⟩ X ⟩ j) -> isNormal (ν-impl p x)
      ν-impl-isNormal = {!!}

      -- ν-impl₁ p x = ν-impl p x , ?

      ν : ∀{k} -> ⟨ Mod X k ⟩ -> ⟨ Mod X k ⟩
      ν (j , id-Q , x) = (j , id-Q , x)
      ν (j , some p , x) = ν-impl p x


      isNormal-ν : ∀{k} -> ∀(x : ⟨ Mod X k ⟩) -> isNormal (ν x)
      isNormal-ν x = {!!}

      ν₁ : ∀{k} -> ⟨ Mod X k ⟩ -> ⟨ Mod-Normal X k ⟩
      ν₁ x = ν x , isNormal-ν x

      idempotent-ν : ∀{k} -> ∀{x : ⟨ Mod X k ⟩} -> ν (ν x) ≡ ν x
      idempotent-ν = {!!}


      write : ∀{k j} -> (e : Edge {{of Q}} j k) -> ⟨ Mod X k ⟩ -> ⟨ Mod X j ⟩
      write e (_ , p , x) = (_ , ` e ` ◆ p , x)


      write-comm-impl-2 : {j k l : K} -> (e : Edge {{of Q}} l k) -> (p : QPath {{of Q}} k j) -> (x : 𝟚-𝒰 +-𝒰 ⟨ ⟨ T ⟩ X ⟩ j) -> (ν-impl (e ∷ p) x ≡-Str write e (ν-impl p x)) +-𝒰 (∑ λ y -> ν-impl p x ≡-Str (_ , id-Q , y))
      write-comm-impl-2 e p (left x) = right (_ , refl)
      write-comm-impl-2 e p (just x) with ν-impl p (right x) | ν-impl-isNormal p (right x)
      ... | .(_ , id-Q , _) | by-[] = right (_ , refl)
      ... | .(_ , id-Q , just _) | by-eval x₁ id-Q = right (_ , refl)
      ... | .(_ , some x₂ , just _) | by-eval x₁ (some x₂) = left refl

      write-comm-impl : {j k l : K} -> (e : Edge {{of Q}} l k) -> (p : QPath {{of Q}} k j) -> (x : 𝟚-𝒰 +-𝒰 ⟨ ⟨ T ⟩ X ⟩ j) -> ν (write e (ν-impl p x)) ≡ ν-impl (e ∷ p) x
      write-comm-impl e p x with write-comm-impl-2 e p x
      ... | left P = {!!}
      write-comm-impl e p (left x) | just (fst₁ , P) = {!!}
      write-comm-impl e p (just x) | just (y , P) with ν-impl p (just x) | P
      write-comm-impl e p (just x) | just (left x' , P) | .(_ , id-Q , left x') | refl-StrId = {!!}
      write-comm-impl e p (just x) | just (just x' , P) | .(_ , id-Q , just x') | refl-StrId with split-+-Str (⟨ ⟨ decompose ⟩ ⟩ _ x')
      ... | left x₁ = {!!}
      write-comm-impl (left x₂) p (just x) | just (just x' , P) | .(_ , id-Q , just x') | refl-StrId | just x₁ = refl
      write-comm-impl (just x₂) p (just x) | just (just x' , P) | .(_ , id-Q , just x') | refl-StrId | just (x'' , x''p) with split-+-Str (⟨ ⟨ decompose ⟩ ⟩ _ x')
      write-comm-impl (just x₂) p (just x) | just (just x' , P) | .(_ , id-Q , just x') | refl-StrId | just (x'' , x''p) | left (x''2 , x''2p) with x''2p ⁻¹ ∙ x''p
      ... | ()
      write-comm-impl (just x₂) p (just x) | just (just x' , P) | .(_ , id-Q , just x') | refl-StrId | just (x'' , x''p) | right (x''2 , x''2p) with x''2p ⁻¹ ∙ x''p
      ... | refl-StrId = refl

      -- write-comm-impl e p (left x) = refl
      -- write-comm-impl e (last nothing) (just x) = refl
      -- write-comm-impl e (last (just x₁)) (just x) = {!!} -- with split-+ (⟨ ⟨ decompose ⟩ ⟩ _ x)
      -- write-comm-impl f (e ∷ p) (just x) with ν-impl p (right x) | ν-impl-isNormal p (right x)
      -- ... | _ , some x₁ , just x₂ | Y = {!!}
      -- ... | _ , id-Q , left x₁ | Y = {!!}
      -- ... | _ , id-Q , just x' | Y with split-+ (⟨ ⟨ decompose ⟩ ⟩ _ x')
      -- ... | left _ = {!!}
      -- write-comm-impl f (left x₁ ∷ p) (just x) | _ , id-Q , just x' | Y | just x'' = {!!}
      -- write-comm-impl f (just x₁ ∷ p) (just x) | _ , id-Q , just x' | Y | just (x'' , _) = {!!}

      -- ... | _ , id-Q , left x₁ = {!!}
      -- ... | _ , some x₂ , left x₁ = {!!}
      -- ... | _ , p' , just x₁ = {!!}

      -- with ν-impl p (right x) | ν-impl (e ∷ p) (right x)
      -- ... | _ , some x₁ , x' | _ , id-Q , left x₂ = {!!}
      -- ... | _ , some x₁ , x' | _ , id-Q , just x₂ = {!!}
      -- ... | _ , some x₁ , x' | _ , some x₂ , x'2 = {!!}
      -- ... | _ , id-Q , left x' | _ , id-Q , left x₁ = {!!}
      -- ... | _ , id-Q , left x' | _ , id-Q , just x₁ = {!!}
      -- ... | _ , id-Q , left x' | _ , some x₁ , left x₂ = {!!}
      -- ... | _ , id-Q , left x' | _ , some x₁ , just x₂ = {!!}
      -- ... | _ , id-Q , just x' | Z = {!!}


      -- with split-+ (⟨ ⟨ decompose ⟩ ⟩ _ x')
      -- ... | left x₁ = {!!}
      -- write-comm-impl f (left x₁ ∷ p) (just x) | _ , id-Q , just x' | just (x'' , _) = {!!}
      -- write-comm-impl f (just x₁ ∷ p) (just x) | _ , id-Q , just x' | just (x'' , _) = {!!}

      -- write-comm-impl f (e ∷ p) (just x) with ν-impl p (right x)
      -- ... | _ , some x₁ , x' = {!!}
      -- ... | _ , id-Q , left x' = {!!}
      -- ... | _ , id-Q , just x' with split-+ (⟨ ⟨ decompose ⟩ ⟩ _ x')
      -- ... | left x₁ = {!!}
      -- write-comm-impl f (left x₁ ∷ p) (just x) | _ , id-Q , just x' | just (x'' , _) = {!!}
      -- write-comm-impl f (just x₁ ∷ p) (just x) | _ , id-Q , just x' | just (x'' , _) = {!!}


      -- write-comm-impl e p (left x) = refl
      -- write-comm-impl f (last (nothing)) (just x) = refl
      -- write-comm-impl f (last (just x₁)) (just x) with split-+ (⟨ ⟨ decompose ⟩ ⟩ _ x)
      -- ... | just _ = refl
      -- ... | left P with split-+ (⟨ ⟨ decompose ⟩ ⟩ _ x)
      -- ... | left _ = refl
      -- ... | just Q = {!!} -- 𝟘-elim (left≢right (snd P ⁻¹ ∙ snd Q))
      -- write-comm-impl f (e ∷ p) (just x) = {!!}

      write-comm : ∀{k j} -> (e : Edge {{of Q}} j k) -> (x : ⟨ Mod X k ⟩)-> ν (write e (ν x)) ≡ ν (write e x)
      write-comm e (j , id-Q , x) = refl
      write-comm e (j , some p , x) = write-comm-impl e p x

      -- write-comm e (j , p , left x) = refl
      -- write-comm e (j , id-Q , just x) = refl
      -- write-comm e (j , some p , just x) = ?

    module _ {X Y : IdxSet K 𝑖} where
      apply : ∀{k} -> (f : X ⟶ ⟨ T ⟩ Y) -> ⟨ Mod X k ⟩ -> ⟨ Mod Y k ⟩
      apply f (_ , p , left x) = (_ , p , left x)
      apply f (_ , p , right x) = (_ , p , right (⟨ f =<< ⟩ _ x))

      apply-comm : ∀{k} -> (f : X ⟶ ⟨ T ⟩ Y) -> (x : ⟨ Mod X k ⟩) -> ν (apply f (ν x)) ≡ ν (apply f x)
      apply-comm f (_ , id-Q , x) = refl
      apply-comm f (_ , some x₁ , x) = {!!}

  𝑺 : IdxSet K 𝑖 -> PSh 𝔇 𝑖
  𝑺 X = mirror-Functor (free-Diagram f)
    where f : QuiverHom (Q) (ForgetCategory (` Set 𝑖 ` ᵒᵖ))
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

      gp : {a b : K} (e : Maybe (Edge {{Dir}} b a)) (x : ⟨ ⟨ 𝑺 X ⟩ a ⟩) →
            ⟨ map {{of 𝑺 Y}} (⩚ e) ⟩ (⟨ g a ⟩ x) ≡
            ⟨ g b ⟩ (⟨ map {{of 𝑺 X}} (⩚ e) ⟩ x)
      gp e ((j , p , just x) , pp) = byFirstP P

       where P : ν (write e (ν (apply f (j , p , just x))))
                  ≡
                ν (apply f (ν (write e (j , p , just x))))
             P = write-comm e (apply f (j , p , just x)) ∙ apply-comm f (write e (j , p , just x)) ⁻¹

      gp e ((j , id-Q , left x) , _) = byFirstP refl


  module _ {X Y : IdxSet K 𝑖} where
    map-𝑺 : (f : X ⟶ ⟨ T ⟩ Y) -> 𝑺 X ⟶ 𝑺 Y
    map-𝑺 f = mirror-Nat (free-Diagram-Natimpl (g f) (λ e x -> gp f e x ⁻¹))





    -- (free-Diagram-Natimpl (g f) (λ e x -> gp f e x))



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




