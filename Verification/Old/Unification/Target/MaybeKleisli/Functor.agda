
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
  IEquiv:โ : {๐ : Category ๐} -> IEquiv (ฮป (a b : โจ ๐ โฉ) -> a โ b)
  IEquiv.refl IEquiv:โ = {!!}
  IEquiv.sym IEquiv:โ = {!!}
  IEquiv._โ_ IEquiv:โ = {!!}

-- module _ {K : ๐ฐ ๐} {๐} where
--   ๐ : Category (๐ โบ โ ๐ , ๐ โ ๐ , ๐ โ ๐)
--   ๐ = Category:IdxSet K ๐
module _ {X : ๐ฐ ๐} {{_ : ICategory X ๐}} {{_ : hasCoproducts ` X `}} where
  assoc-l-+ : โ{a b c : X} -> (a + b) + c โ a + (b + c)
  assoc-l-+ = {!!}

  assoc-r-+ : โ{a b c : X} -> a + (b + c) โ (a + b) + c
  assoc-r-+ = assoc-l-+ โปยน

instance
  I1Category:Kleisli : {๐ : Category ๐} {{_ : I1Category ๐}} {T : Monad ๐} -> I1Category (๐ โ T)
  I1Category.ISet:Hom I1Category:Kleisli = {!!}
  I1Category.โฃโโก I1Category:Kleisli = {!!}

module _ {๐ : Category ๐} {{_ : I1Category ๐}}
         {{_ : hasCoproducts ๐}}
         {{_ : hasInitial ๐}}
         {{_ : Terminal ๐}}
         where

  infixl 180 _โ
  _โ : Monad ๐ -> Monad ๐
  _โ T = Monad:EitherT ๐ T


  module _ (T : Monad ๐)  where
    F = ๐ฒ+ ๐ T
    instance _ = of F
    instance _ = of Category:Kleisli T
    instance _ = of Category:Kleisli (T โ)

    module _ {a b x : Kleisli T} {f g : Hom a b} where

      module _ {{C : isCoequalizer f g x}} where

        lem-1 : isCoequalizer (map f) (map g) (โจ F โฉ x)
        isCoequalizer.ฯ-Coeq lem-1 = map (ฯ-Coeq)
        isCoequalizer.โฃ-Coeq lem-1 = functoriality-โ โปยน โ functoriality-โฃ โฃ-Coeq โ functoriality-โ
        โจ isCoequalizer.elim-Coeq lem-1 {c} h p  โฉ = โจ elim-Coeq (h') y โฉ
          where h' : Hom {{of ๐ โ T}} _ `(๐ + โจ c โฉ)`
                h' = ` โจ h โฉ `

                y : โจ f โฉ โ map โจ h' โฉ โ join {{of T}} โฃ โจ g โฉ โ map โจ h' โฉ โ join {{of T}}
                y =   VCCMIC-1.lem-1 ๐ T f ` โจ h โฉ ` โปยน
                    โ p
                    โ VCCMIC-1.lem-1 ๐ T g ` โจ h โฉ `
        of isCoequalizer.elim-Coeq lem-1 h p = record {}
        isCoequalizer.reduce-Coeq lem-1 h p =
          let P = โจ map {{of F}} ฯ-Coeq โฉ โ (map {{of โจ T โ โฉ}} โจ elim-Coeq _ _ โฉ) โ join {{of (T โ)}}

                  โฃโจ VCCMIC-1.lem-1 ๐ T _ _ โฉ

                  โจ ฯ-Coeq โฉ โ map _ โ join {{of T}}

                  โฃโจ reduce-Coeq _ _ โฉ

                  โจ h โฉ โ
          in P
        isCoequalizer.expand-Coeq lem-1 h p =
          let P : โจ h โฉ โฃ โจ elim-Coeq (ฯ-Coeq โ ` โจ h โฉ `) _ โฉ
              P = expand-Coeq ` โจ h โฉ ` ((assoc-r-โ โ (โฃ-Coeq โ refl) โ assoc-l-โ))

              R : (ฯ-Coeq โ ` โจ h โฉ `) โฃ (` โจ ฯ-Coeq โฉ โ map ฮนโ โ map {{of โจ T โ โฉ}} โจ h โฉ โ join {{of T โ}} `)
              R = VCCMIC-1.lem-1 ๐ T _ _ โปยน

              -- Q00 : โจ h โฉ โฃ โจ elim-Coeq (` โจ ฯ-Coeq โฉ โ map ฮนโ โ map {{of โจ T โ โฉ}} โจ h โฉ โ join {{of T โ}} `) _ โฉ
              -- Q00 = subst-โฃ (ฮป f -> โจ h โฉ โฃ โจ elim-Coeq f _ โฉ) R P

              Q0 : โจ h โฉ โฃ โจ elim-Coeq (` โจ ฯ-Coeq โฉ โ map ฮนโ โ map {{of โจ T โ โฉ}} โจ h โฉ โ join {{of T โ}} `) _ โฉ
              Q0 = {!!}

              Q1 : โจ h โฉ โฃ โจ elim-Coeq (` โจ ` โจ ฯ-Coeq โฉ โ map ฮนโ ` โ h โฉ `) _ โฉ
              Q1 = Q0

              Q2 : โจ h โฉ โฃ โจ elim-Coeq (` โจ map ฯ-Coeq โ h โฉ `) _ โฉ
              Q2 = Q1
          in Q2

      module _ {{C : isCoequalizer (map f) (map g) ` โจ x โฉ `}} where

        lem-2 : (h : Hom {{of ๐ โ T}} b x) -> (โจ h โฉ โ map ฮนโ โฃ โจ ฯ-Coeq โฉ) -> isCoequalizer f g x
        lem-2 = {!!}


    lem-3 : โ{a : โจ ๐ โฉ} -> isFinite {๐ = ๐ โ T} ` a ` -> isFinite {๐ = ๐ โ T โ} ` a `
    lem-3 = {!!}
    -- hasLift-F (lem-3 {a} P) {b} {c} f with hasLift-F P f'
    --   where f' : a โถ โจ โจ T โฉ โฉ (b + (๐ + c))
    --         f' = f โ map g
    --           where g : (๐ + (b + c)) โถ (b + (๐ + c))
    --                 g = {!!}
    -- ... | yes p =
    --   let f' = lift p

    --   in yes (record { lift = f' ; factors-lift = {!!} })
    -- ... | no ยฌp = {!!}


    lem-4 : hasUnification (๐ โ T โ) -> hasUnification (๐ โ T)
    lem-4 = {!!}
{-
    unify (lem-4 algo) P f g with unify algo (lem-3 P) (map {{of F}} f) (map g)
    ... | no ยฌp = no (ฮป X -> ยฌp (โ_ โจ X โฉ {{lem-1}}))
    ... | yes p with hasLift-F P โจ ฯ-Coeq โฉ
    ... | yes p2 =
      let f' = lift p2
      in yes (โ_ โจ p โฉ {{lem-2 ` f' ` (factors-lift p2)}})
    ... | no ยฌp = no (ฮป x ->
        let P = VUD-1.lem-2 T f g โจ x โฉ {!!}

            -- | By using |VUD-1.lem2| we show that we can get a function from |x| to |T p|
            h : Hom {{of ๐}} โจ x โฉ (โจ โจ T โฉ โฉ โจ p โฉ)
            h = {!!}


        in {!!})
-}






    -- isCoequalizer.ฯ-! (lem::preserves-coequalizers C) =
    --   let X = isCoequalizer.ฯ-! {{of ๐ โ T}} C
    --   in map {{of F}} X
    -- isCoequalizer.coequalizes (lem::preserves-coequalizers C) = {!!}
    -- isCoequalizer.elim-! (lem::preserves-coequalizers C) = {!!}





  -- module _ (T'' : โจ ๐ โฉ โถ โจ ๐ โฉ) {{T' : IFunctor ๐ ๐ T''}} {{TX : IMonad (functor T'' {{T'}})}} where
  --   T : Monad ๐
  --   T = monad ` T'' ` {{TX}}



    -- F : ๐ โ T โถ ๐ โ T โ
    -- โจ F โฉ a = a
    -- IFunctor.map (of F) f = f โ map {{of โจ T โฉ}} return
    -- IFunctor.functoriality-id (of F) = refl
    -- IFunctor.functoriality-โ (of F) {f = f} {g} =
    --   let ET = Functor:EitherT _ T
    --       P : (f โ map g โ join) โ map ฮนโ โฃ (f โ map ฮนโ) โ (map {{of ET}} (g โ map ฮนโ)) โ (map ([ ฮนโ โ return , id ]) โ join)
    --       P = {!!}
          {-
          P = {!!} โฃโจ {!!} โฉ

              f โ (map g โ (map (map ฮนโ โ (ฮนโ โ ([ ฮนโ โ return , id ]))) โ join))

              โฃโจ refl โ (refl โ (functoriality-โฃ assoc-r-โ โ refl)) โฉ

              f โ (map g โ (map ((map ฮนโ โ ฮนโ) โ ([ ฮนโ โ return , id ])) โ join))

              โฃโจ refl โ (refl โ ((functoriality-โฃ (naturality {{INatural:return}} _ โปยน โ refl)) โ refl)) โฉ

              f โ (map g โ (map ((ฮนโ โ map (map ฮนโ)) โ ([ ฮนโ โ return , id ])) โ join))

              โฃโจ refl โ (refl โ (functoriality-โ โ refl)) โฉ

              f โ (map g โ ((map (ฮนโ โ map (map ฮนโ))) โ map ([ ฮนโ โ return , id ]) โ join))

              โฃโจ refl โ (refl โ assoc-l-โ) โฉ

              f โ (map g โ ((map (ฮนโ โ map (map ฮนโ))) โ (map ([ ฮนโ โ return , id ]) โ join)))

              โฃโจ refl โ (assoc-r-โ) โฉ

              f โ ((map g โ (map (ฮนโ โ map (map ฮนโ)))) โ (map ([ ฮนโ โ return , id ]) โ join))

              โฃโจ refl โ (refl โ functoriality-โ โ refl) โฉ

              f โ ((map g โ (map ฮนโ โ map {{of ET}} (map ฮนโ))) โ (map ([ ฮนโ โ return , id ]) โ join))

              โฃโจ refl โ (assoc-r-โ โ refl) โฉ

              f โ (((map g โ map ฮนโ) โ map {{of ET}} (map ฮนโ)) โ (map ([ ฮนโ โ return , id ]) โ join))

              โฃโจ assoc-r-โ โฉ

              (f โ ((map g โ map ฮนโ) โ map {{of ET}} (map ฮนโ))) โ (map ([ ฮนโ โ return , id ]) โ join)

              โฃโจ (refl โ (functoriality-โ โปยน โ refl)) โ refl โฉ

              (f โ (map (g โ ฮนโ) โ map {{of ET}} (map ฮนโ))) โ (map ([ ฮนโ โ return , id ]) โ join)

              โฃโจ (refl โ (functoriality-โฃ (naturality {{INatural:return}} g โปยน) โ refl)) โ refl โฉ

              (f โ (map (ฮนโ โ map g) โ map {{of ET}} (map ฮนโ))) โ (map ([ ฮนโ โ return , id ]) โ join)

              โฃโจ (refl โ (functoriality-โ โ refl)) โ refl โฉ

              (f โ (map ฮนโ โ map {{of ET}} g โ map {{of ET}} (map ฮนโ))) โ (map ([ ฮนโ โ return , id ]) โ join)

              โฃโจ (refl โ assoc-l-โ) โ refl โฉ

              (f โ (map ฮนโ โ (map {{of ET}} g โ map {{of ET}} (map ฮนโ)))) โ (map ([ ฮนโ โ return , id ]) โ join)

              โฃโจ assoc-r-โ โ refl โฉ

              (f โ map ฮนโ) โ (map {{of ET}} g โ map {{of ET}} (map ฮนโ)) โ (map ([ ฮนโ โ return , id ]) โ join)

              โฃโจ refl โ functoriality-โ {{of ET}} โปยน โ refl โฉ

              (f โ map ฮนโ) โ (map {{of ET}} (g โ map ฮนโ)) โ (map ([ ฮนโ โ return , id ]) โ join) โ
              -}

      -- in P
    -- IFunctor.functoriality-โฃ (of F) = {!!}

  -- infixl 180 _โ
  -- _โ : Monad ๐ -> Monad ๐
  -- _โ T = Monad:EitherT ๐ T

  -- module _ (T : Monad ๐) where
  --   F : ๐ โ T โถ ๐ โ T โ
  --   โจ F โฉ a = a
  --   IFunctor.map (of F) f = f โ map {{of โจ T โฉ}} return
  --   IFunctor.functoriality-id (of F) = {!!}
  --   IFunctor.functoriality-โ (of F) = {!!}
  --   IFunctor.functoriality-โฃ (of F) = {!!}





