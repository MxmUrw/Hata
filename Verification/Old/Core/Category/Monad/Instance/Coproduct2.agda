

module Verification.Old.Core.Category.Monad.Instance.Coproduct2 where

open import Verification.Conventions
open import Verification.Old.Core.Category.Definition
open import Verification.Old.Core.Category.Proper
open import Verification.Old.Core.Category.Instance.SmallCategories
open import Verification.Old.Core.Category.Instance.Type
open import Verification.Old.Core.Category.Instance.Cat
open import Verification.Old.Core.Category.Monad2.Definition
open import Verification.Old.Core.Category.Limit.Specific
open import Verification.Old.Core.Category.Limit.Kan.Terminal
open import Verification.Old.Core.Category.Lift


-- join-+-𝒰 : ∀{X A : 𝒰 𝑖} -> X +-𝒰 (X +-𝒰 A) -> X +-𝒰 A
-- join-+-𝒰 (left x) = left x
-- join-+-𝒰 (right x) = x

-- second-+-𝒰 : ∀{A B X : 𝒰 𝑖} -> (A -> B) -> (X +-𝒰 A) -> (X +-𝒰 B)
-- second-+-𝒰 f (left x) = left x
-- second-+-𝒰 f (right a) = right (f a)

-- first-+-𝒰 : ∀{A B X : 𝒰 𝑖} -> (A -> B) -> (A +-𝒰 X) -> (B +-𝒰 X)
-- first-+-𝒰 f (left a) = left (f a)
-- first-+-𝒰 f (right x) = right x

-- instance
--   IFunctor:+-𝒰 : ∀{X : 𝒰 𝑖} -> IFunctor (Category:𝒰 𝑖) (Category:𝒰 𝑖) (X +-𝒰_)
--   IFunctor.map IFunctor:+-𝒰 = second-+-𝒰
--   IFunctor.functoriality-id IFunctor:+-𝒰 = {!!}
--   IFunctor.functoriality-◆ IFunctor:+-𝒰 = {!!}
--   IFunctor.functoriality-≣ IFunctor:+-𝒰 = {!!}

-- instance
--   IMonad:+-𝒰 : ∀{X : 𝒰₀} -> IMonad (⌘ X +-𝒰_)
--   -- IMonad.FunctorInstance IMonad:+-𝒰 = IFunctor:+-𝒰
--   IMonad.return IMonad:+-𝒰 = right
--   IMonad.INatural:return IMonad:+-𝒰 = {!!}
--   IMonad.join IMonad:+-𝒰 = join-+-𝒰
--   IMonad.INatural:join IMonad:+-𝒰 = {!!}
--   IMonad.unit-l-join IMonad:+-𝒰 = {!!}
--   IMonad.unit-r-join IMonad:+-𝒰 = {!!}
--   IMonad.assoc-join IMonad:+-𝒰 = {!!}



-- module _ {X : 𝒰 𝑖} {{XX : ICategory X 𝑗}} where
--   module _ {{_ : I1Category ` X `}} {{_ : hasCoproducts ` X `}} where
--     𝒞 = category X {{XX}}
module _ {𝒞 : Category 𝑖} {{_ : hasCoproducts 𝒞}} where
  module _ where

    Functor:Either : ∀(x : ⟨ 𝒞 ⟩) -> 𝒞 ⟶ 𝒞
    ⟨ Functor:Either x ⟩ b = x + b
    IFunctor.map (of Functor:Either x) f = map {{of Functor:+}} (id , f)
    IFunctor.functoriality-id (of Functor:Either x) = {!!}
    IFunctor.functoriality-◆ (of Functor:Either x) = {!!}
    IFunctor.functoriality-≣ (of Functor:Either x) = {!!}

    instance
      IFunctor:Either : ∀{x} -> IFunctor 𝒞 𝒞 (x +_)
      IFunctor:Either {x = x} = of Functor:Either x

  -- instance IFunctor:Either = #openstruct Functor:Either

    private
      return-+ : ∀{a b : ⟨ 𝒞 ⟩} -> a ⟶ b + a
      return-+ {a} {b} = ι₁

      join-+ : ∀{a x : ⟨ 𝒞 ⟩} -> (x + (x + a)) ⟶ (x + a)
      join-+ {a} {x} = [ ι₀ , id ]

    Monad:Either : ∀(x : ⟨ 𝒞 ⟩) -> Monad 𝒞
    ⟨ Monad:Either x ⟩ = Functor:Either x
    IMonad.return (of Monad:Either x) = return-+
    IMonad.join (of Monad:Either x) = join-+
    IMonad.INatural:return (of Monad:Either x) = {!!}
    IMonad.INatural:join (of Monad:Either x) = {!!}
    IMonad.unit-l-join (of Monad:Either x) = {!!}
    IMonad.unit-r-join (of Monad:Either x) = {!!}
    IMonad.assoc-join (of Monad:Either x) = {!!}

    instance
      IMonad:Either : ∀{x : ⟨ 𝒞 ⟩} -> IMonad (x +_)
      IMonad:Either {x = x} = of Monad:Either x

    private
      _◇_ = Functor:comp-Cat

    module _ (x : ⟨ 𝒞 ⟩) (T : Monad 𝒞) where

      Functor:EitherT : Functor 𝒞 𝒞
      Functor:EitherT = ` x +_ ` ◇ ⟨ T ⟩
      -- instance
      --   IFunctor:EitherT : IFunctor 𝒞 𝒞 (λ a -> ⟨ T ⟩ (x + a))
      --   IFunctor:EitherT = {!!}

      Monad:EitherT : Monad 𝒞
      ⟨ Monad:EitherT ⟩ = Functor:EitherT
      IMonad.return (of Monad:EitherT) = return ◆ map return
      IMonad.join (of Monad:EitherT) = map ([ ι₀ ◆ return , id ]) ◆ join
      IMonad.INatural:return (of Monad:EitherT) = {!!}
      IMonad.INatural:join (of Monad:EitherT) = {!!}
      IMonad.unit-l-join (of Monad:EitherT) = {!!}
      IMonad.unit-r-join (of Monad:EitherT) = {!!}
      IMonad.assoc-join (of Monad:EitherT) = {!!}

-- {{XX : ICategory X 𝑗}} 
  -- module _ {{_ : I1Category ` X `}} {{_ : hasCoproducts ` X `}} where
module _ {𝒞 : Category 𝑖} {{_ : hasCoproducts 𝒞}} where
  module _ where
    module _ {{_ : Terminal 𝒞}} where
      -- infixl 180 _₊
      -- _₊ : Monad 𝒞 -> Monad 𝒞
      -- _₊ T = Monad:EitherT 𝟙 T

      -- module _ (T'' : ⟨ 𝒞 ⟩ ⟶ ⟨ 𝒞 ⟩) {{T' : IFunctor 𝒞 𝒞 T''}} {{TX : IMonad (T'')}} where
      module _ (T : ⟨ 𝒞 ⟩ ⟶ ⟨ 𝒞 ⟩) {{_ : IFunctor 𝒞 𝒞 T}} {{_ : IMonad {𝒞 = 𝒞} T}} where
        -- T : Monad 𝒞
        -- T = monad ` T'' ` {{TX}}

        F : ∀(x : ⟨ 𝒞 ⟩) -> 𝒞 ⌄ monad T ⟶ {!!} -- 𝒞 ⌄ (Monad:EitherT x ` T `)
        F = {!!}
        -- ⟨ F x ⟩ a = a
        -- IFunctor.map (of F x) f = f ◆ map {{of ⟨ T ⟩}} return
        -- IFunctor.functoriality-id (of F x) = refl
        -- IFunctor.functoriality-◆ (of F x) {f = f} {g} =
        --   let -- ET = Functor:EitherT _ T
        --       P : (f ◆ map {{T'}} g ◆ join) ◆ map ι₁ ≣ (f ◆ map ι₁) ◆ (map {{IFunctor:EitherT _ T}} (g ◆ map ι₁)) ◆ (map ([ ι₀ ◆ return , id ]) ◆ join)
        --       P = {!!}

        --   in P
        -- IFunctor.functoriality-≣ (of F x) = {!!}

  -- instance
    -- IFunctor:EitherT : ∀{x : ⟨ 𝒞 ⟩} -> ∀{T : Monad 𝒞} -> IFunctor 𝒞 𝒞 (λ a -> ⟨ ⟨ T ⟩ ⟩ (x + a) )
    -- IFunctor:EitherT {x = x} {T} = of Functor:EitherT x T

    -- IMonad:EitherT : ∀{x : ⟨ 𝒞 ⟩} -> ∀{T : Monad 𝒞} -> IMonad (Functor:EitherT x T)
    -- IMonad:EitherT {x = x} {T} = of Monad:EitherT x T

{-
  module _ {{_ : Terminal 𝒞}} where
    infixl 180 _₊
    _₊ : Monad 𝒞 -> Monad 𝒞
    _₊ T = Monad:EitherT 𝟙 T

    module _ (T : Monad 𝒞) where
      F : 𝒞 ⌄ T ⟶ 𝒞 ⌄ T ₊
      ⟨ F ⟩ a = a
      IFunctor.map (of F) f = f ◆ map {{of ⟨ T ⟩}} return
      IFunctor.functoriality-id (of F) = refl
      IFunctor.functoriality-◆ (of F) {f = f} {g} =
        let ET = Functor:EitherT _ T
            P : (f ◆ map g ◆ join) ◆ map ι₁ ≣ (f ◆ map ι₁) ◆ (map {{of ET}} (g ◆ map ι₁)) ◆ (map ([ ι₀ ◆ return , id ]) ◆ join)
            P = {!!} ≣⟨ {!!} ⟩

                f ◆ (map g ◆ (map (map ι₁ ◆ (ι₁ ◆ ([ ι₀ ◆ return , id ]))) ◆ join))

                ≣⟨ refl ◈ (refl ◈ (functoriality-≣ assoc-r-◆ ◈ refl)) ⟩

                f ◆ (map g ◆ (map ((map ι₁ ◆ ι₁) ◆ ([ ι₀ ◆ return , id ])) ◆ join))

                ≣⟨ refl ◈ (refl ◈ ((functoriality-≣ (naturality {{INatural:return}} _ ⁻¹ ◈ refl)) ◈ refl)) ⟩

                f ◆ (map g ◆ (map ((ι₁ ◆ map (map ι₁)) ◆ ([ ι₀ ◆ return , id ])) ◆ join))

                ≣⟨ refl ◈ (refl ◈ (functoriality-◆ ◈ refl)) ⟩

                f ◆ (map g ◆ ((map (ι₁ ◆ map (map ι₁))) ◆ map ([ ι₀ ◆ return , id ]) ◆ join))

                ≣⟨ refl ◈ (refl ◈ assoc-l-◆) ⟩

                f ◆ (map g ◆ ((map (ι₁ ◆ map (map ι₁))) ◆ (map ([ ι₀ ◆ return , id ]) ◆ join)))

                ≣⟨ refl ◈ (assoc-r-◆) ⟩

                f ◆ ((map g ◆ (map (ι₁ ◆ map (map ι₁)))) ◆ (map ([ ι₀ ◆ return , id ]) ◆ join))

                ≣⟨ refl ◈ (refl ◈ functoriality-◆ ◈ refl) ⟩

                f ◆ ((map g ◆ (map ι₁ ◆ map {{of ET}} (map ι₁))) ◆ (map ([ ι₀ ◆ return , id ]) ◆ join))

                ≣⟨ refl ◈ (assoc-r-◆ ◈ refl) ⟩

                f ◆ (((map g ◆ map ι₁) ◆ map {{of ET}} (map ι₁)) ◆ (map ([ ι₀ ◆ return , id ]) ◆ join))

                ≣⟨ assoc-r-◆ ⟩

                (f ◆ ((map g ◆ map ι₁) ◆ map {{of ET}} (map ι₁))) ◆ (map ([ ι₀ ◆ return , id ]) ◆ join)

                ≣⟨ (refl ◈ (functoriality-◆ ⁻¹ ◈ refl)) ◈ refl ⟩

                (f ◆ (map (g ◆ ι₁) ◆ map {{of ET}} (map ι₁))) ◆ (map ([ ι₀ ◆ return , id ]) ◆ join)

                ≣⟨ (refl ◈ (functoriality-≣ (naturality {{INatural:return}} g ⁻¹) ◈ refl)) ◈ refl ⟩

                (f ◆ (map (ι₁ ◆ map g) ◆ map {{of ET}} (map ι₁))) ◆ (map ([ ι₀ ◆ return , id ]) ◆ join)

                ≣⟨ (refl ◈ (functoriality-◆ ◈ refl)) ◈ refl ⟩

                (f ◆ (map ι₁ ◆ map {{of ET}} g ◆ map {{of ET}} (map ι₁))) ◆ (map ([ ι₀ ◆ return , id ]) ◆ join)

                ≣⟨ (refl ◈ assoc-l-◆) ◈ refl ⟩

                (f ◆ (map ι₁ ◆ (map {{of ET}} g ◆ map {{of ET}} (map ι₁)))) ◆ (map ([ ι₀ ◆ return , id ]) ◆ join)

                ≣⟨ assoc-r-◆ ◈ refl ⟩

                (f ◆ map ι₁) ◆ (map {{of ET}} g ◆ map {{of ET}} (map ι₁)) ◆ (map ([ ι₀ ◆ return , id ]) ◆ join)

                ≣⟨ refl ◈ functoriality-◆ {{of ET}} ⁻¹ ◈ refl ⟩

                (f ◆ map ι₁) ◆ (map {{of ET}} (g ◆ map ι₁)) ◆ (map ([ ι₀ ◆ return , id ]) ◆ join) ∎

        in P
      IFunctor.functoriality-≣ (of F) = {!!}

-}


