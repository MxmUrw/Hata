
module Verification.Unification.Target.MaybeKleisli.Functor where

open import Verification.Conventions hiding (lift)
open import Verification.Core.Type
-- open import Verification.Core.Algebra
open import Verification.Core.Order
open import Verification.Core.Category.Definition
open import Verification.Core.Category.Functor.Presheaf
open import Verification.Core.Category.Monad
open import Verification.Core.Category.Quiver
open import Verification.Core.Category.FreeCategory
open import Verification.Core.Category.Functor.Category
open import Verification.Core.Category.Instance.Type
open import Verification.Core.Category.Instance.Cat
open import Verification.Core.Category.Instance.SmallCategories
open import Verification.Core.Category.Instance.TypeProperties
open import Verification.Core.Category.Instance.Set
open import Verification.Core.Category.Instance.Kleisli
-- open import Verification.Core.Category.Instance.IdxSet
open import Verification.Core.Category.Limit.Kan
open import Verification.Core.Category.Limit.Specific
open import Verification.Core.Category.Monad
open import Verification.Core.Category.Proper
open import Verification.Core.Category.Iso hiding (Notation-Inverse:Iso)
open import Verification.Core.Homotopy.Level
open import Verification.Unification.Definition
open import Verification.Unification.RecAccessible


instance
  IEquiv:≅ : {𝒞 : Category 𝑖} -> IEquiv (λ (a b : ⟨ 𝒞 ⟩) -> a ≅ b)
  IEquiv.refl IEquiv:≅ = {!!}
  IEquiv.sym IEquiv:≅ = {!!}
  IEquiv._∙_ IEquiv:≅ = {!!}

-- module _ {K : 𝒰 𝑗} {𝑖} where
--   𝒞 : Category (𝑖 ⁺ ⊔ 𝑗 , 𝑖 ⊔ 𝑗 , 𝑖 ⊔ 𝑗)
--   𝒞 = Category:IdxSet K 𝑖
module _ {X : 𝒰 𝑖} {{_ : ICategory X 𝑗}} {{_ : hasCoproducts ` X `}} where
  assoc-l-+ : ∀{a b c : X} -> (a + b) + c ≅ a + (b + c)
  assoc-l-+ = {!!}

  assoc-r-+ : ∀{a b c : X} -> a + (b + c) ≅ (a + b) + c
  assoc-r-+ = assoc-l-+ ⁻¹

instance
  I1Category:Kleisli : {𝒞 : Category 𝑖} {{_ : I1Category 𝒞}} {T : Monad 𝒞} -> I1Category (𝒞 ⌄ T)
  I1Category.ISet:Hom I1Category:Kleisli = {!!}
  I1Category.≣→≡ I1Category:Kleisli = {!!}

module _ {𝒞 : Category 𝑖} {{_ : I1Category 𝒞}}
         {{_ : hasCoproducts 𝒞}}
         {{_ : hasInitial 𝒞}}
         {{_ : Terminal 𝒞}}
         where

  infixl 180 _₊
  _₊ : Monad 𝒞 -> Monad 𝒞
  _₊ T = Monad:EitherT 𝟙 T


  module _ (T : Monad 𝒞)  where
    F = 𝑲+ 𝟙 T
    instance _ = of F
    instance _ = of Category:Kleisli T
    instance _ = of Category:Kleisli (T ₊)

    module _ {a b x : Kleisli T} {f g : Hom a b} where

      module _ {{C : isCoequalizer f g x}} where

        lem-1 : isCoequalizer (map f) (map g) (⟨ F ⟩ x)
        isCoequalizer.π-Coeq lem-1 = map (π-Coeq)
        isCoequalizer.≣-Coeq lem-1 = functoriality-◆ ⁻¹ ∙ functoriality-≣ ≣-Coeq ∙ functoriality-◆
        ⟨ isCoequalizer.elim-Coeq lem-1 {c} h p  ⟩ = ⟨ elim-Coeq (h') y ⟩
          where h' : Hom {{of 𝒞 ⌄ T}} _ `(𝟙 + ⟨ c ⟩)`
                h' = ` ⟨ h ⟩ `

                y : ⟨ f ⟩ ◆ map ⟨ h' ⟩ ◆ join {{of T}} ≣ ⟨ g ⟩ ◆ map ⟨ h' ⟩ ◆ join {{of T}}
                y =   VCCMIC-1.lem-1 𝟙 T f ` ⟨ h ⟩ ` ⁻¹
                    ∙ p
                    ∙ VCCMIC-1.lem-1 𝟙 T g ` ⟨ h ⟩ `
        of isCoequalizer.elim-Coeq lem-1 h p = record {}
        isCoequalizer.reduce-Coeq lem-1 h p =
          let P = ⟨ map {{of F}} π-Coeq ⟩ ◆ (map {{of ⟨ T ₊ ⟩}} ⟨ elim-Coeq _ _ ⟩) ◆ join {{of (T ₊)}}

                  ≣⟨ VCCMIC-1.lem-1 𝟙 T _ _ ⟩

                  ⟨ π-Coeq ⟩ ◆ map _ ◆ join {{of T}}

                  ≣⟨ reduce-Coeq _ _ ⟩

                  ⟨ h ⟩ ∎
          in P
        isCoequalizer.expand-Coeq lem-1 h p =
          let P : ⟨ h ⟩ ≣ ⟨ elim-Coeq (π-Coeq ◆ ` ⟨ h ⟩ `) _ ⟩
              P = expand-Coeq ` ⟨ h ⟩ ` ((assoc-r-◆ ∙ (≣-Coeq ◈ refl) ∙ assoc-l-◆))

              R : (π-Coeq ◆ ` ⟨ h ⟩ `) ≣ (` ⟨ π-Coeq ⟩ ◆ map ι₁ ◆ map {{of ⟨ T ₊ ⟩}} ⟨ h ⟩ ◆ join {{of T ₊}} `)
              R = VCCMIC-1.lem-1 𝟙 T _ _ ⁻¹

              -- Q00 : ⟨ h ⟩ ≣ ⟨ elim-Coeq (` ⟨ π-Coeq ⟩ ◆ map ι₁ ◆ map {{of ⟨ T ₊ ⟩}} ⟨ h ⟩ ◆ join {{of T ₊}} `) _ ⟩
              -- Q00 = subst-≣ (λ f -> ⟨ h ⟩ ≣ ⟨ elim-Coeq f _ ⟩) R P

              Q0 : ⟨ h ⟩ ≣ ⟨ elim-Coeq (` ⟨ π-Coeq ⟩ ◆ map ι₁ ◆ map {{of ⟨ T ₊ ⟩}} ⟨ h ⟩ ◆ join {{of T ₊}} `) _ ⟩
              Q0 = {!!}

              Q1 : ⟨ h ⟩ ≣ ⟨ elim-Coeq (` ⟨ ` ⟨ π-Coeq ⟩ ◆ map ι₁ ` ◆ h ⟩ `) _ ⟩
              Q1 = Q0

              Q2 : ⟨ h ⟩ ≣ ⟨ elim-Coeq (` ⟨ map π-Coeq ◆ h ⟩ `) _ ⟩
              Q2 = Q1
          in Q2

      module _ {{C : isCoequalizer (map f) (map g) ` ⟨ x ⟩ `}} where

        lem-2 : (h : Hom {{of 𝒞 ⌄ T}} b x) -> (⟨ h ⟩ ◆ map ι₁ ≣ ⟨ π-Coeq ⟩) -> isCoequalizer f g x
        lem-2 = {!!}


    lem-3 : ∀{a : ⟨ 𝒞 ⟩} -> isFinite {𝒞 = 𝒞 ⌄ T} ` a ` -> isFinite {𝒞 = 𝒞 ⌄ T ₊} ` a `
    lem-3 = {!!}
    -- hasLift-F (lem-3 {a} P) {b} {c} f with hasLift-F P f'
    --   where f' : a ⟶ ⟨ ⟨ T ⟩ ⟩ (b + (𝟙 + c))
    --         f' = f ◆ map g
    --           where g : (𝟙 + (b + c)) ⟶ (b + (𝟙 + c))
    --                 g = {!!}
    -- ... | yes p =
    --   let f' = lift p

    --   in yes (record { lift = f' ; factors-lift = {!!} })
    -- ... | no ¬p = {!!}


    lem-4 : hasUnification (𝒞 ⌄ T ₊) -> hasUnification (𝒞 ⌄ T)
    lem-4 = {!!}
{-
    unify (lem-4 algo) P f g with unify algo (lem-3 P) (map {{of F}} f) (map g)
    ... | no ¬p = no (λ X -> ¬p (⌘_ ⟨ X ⟩ {{lem-1}}))
    ... | yes p with hasLift-F P ⟨ π-Coeq ⟩
    ... | yes p2 =
      let f' = lift p2
      in yes (⌘_ ⟨ p ⟩ {{lem-2 ` f' ` (factors-lift p2)}})
    ... | no ¬p = no (λ x ->
        let P = VUD-1.lem-2 T f g ⟨ x ⟩ {!!}

            -- | By using |VUD-1.lem2| we show that we can get a function from |x| to |T p|
            h : Hom {{of 𝒞}} ⟨ x ⟩ (⟨ ⟨ T ⟩ ⟩ ⟨ p ⟩)
            h = {!!}


        in {!!})
-}






    -- isCoequalizer.π-! (lem::preserves-coequalizers C) =
    --   let X = isCoequalizer.π-! {{of 𝒞 ⌄ T}} C
    --   in map {{of F}} X
    -- isCoequalizer.coequalizes (lem::preserves-coequalizers C) = {!!}
    -- isCoequalizer.elim-! (lem::preserves-coequalizers C) = {!!}





  -- module _ (T'' : ⟨ 𝒞 ⟩ ⟶ ⟨ 𝒞 ⟩) {{T' : IFunctor 𝒞 𝒞 T''}} {{TX : IMonad (functor T'' {{T'}})}} where
  --   T : Monad 𝒞
  --   T = monad ` T'' ` {{TX}}



    -- F : 𝒞 ⌄ T ⟶ 𝒞 ⌄ T ₊
    -- ⟨ F ⟩ a = a
    -- IFunctor.map (of F) f = f ◆ map {{of ⟨ T ⟩}} return
    -- IFunctor.functoriality-id (of F) = refl
    -- IFunctor.functoriality-◆ (of F) {f = f} {g} =
    --   let ET = Functor:EitherT _ T
    --       P : (f ◆ map g ◆ join) ◆ map ι₁ ≣ (f ◆ map ι₁) ◆ (map {{of ET}} (g ◆ map ι₁)) ◆ (map ([ ι₀ ◆ return , id ]) ◆ join)
    --       P = {!!}
          {-
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
              -}

      -- in P
    -- IFunctor.functoriality-≣ (of F) = {!!}

  -- infixl 180 _₊
  -- _₊ : Monad 𝒞 -> Monad 𝒞
  -- _₊ T = Monad:EitherT 𝟙 T

  -- module _ (T : Monad 𝒞) where
  --   F : 𝒞 ⌄ T ⟶ 𝒞 ⌄ T ₊
  --   ⟨ F ⟩ a = a
  --   IFunctor.map (of F) f = f ◆ map {{of ⟨ T ⟩}} return
  --   IFunctor.functoriality-id (of F) = {!!}
  --   IFunctor.functoriality-◆ (of F) = {!!}
  --   IFunctor.functoriality-≣ (of F) = {!!}





