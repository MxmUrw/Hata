
module Verification.Unification.Definition where

open import Verification.Conventions hiding (lift)
open import Verification.Core.Type
-- open import Verification.Core.Algebra
open import Verification.Core.Order
open import Verification.Core.Category.Definition
open import Verification.Core.Category.Instance.Kleisli
open import Verification.Core.Category.Iso
open import Verification.Core.Category.Monad
open import Verification.Core.Category.Limit.Specific.Coequalizer
open import Verification.Core.Category.Limit.Specific.Initial
-- open import Verification.Core.Category.Quiver
-- open import Verification.Core.Category.FreeCategory
-- open import Verification.Core.Category.Functor
-- open import Verification.Core.Category.Instance.Type
-- open import Verification.Core.Category.Instance.SmallCategories
-- open import Verification.Core.Category.Instance.TypeProperties
-- open import Verification.Core.Category.Instance.Set
open import Verification.Core.Category.Limit.Specific.Coproduct
-- open import Verification.Core.Category.Monad
-- open import Verification.Unification.RecAccessible
-- open import Verification.Core.Homotopy.Level

-- module _ {X : ๐ฐ ๐} {{_ : ICategory X ๐}} where
--   Cone-Coeq : โ{a b : X} -> (f g : a โถ b) -> ๐ฐ _
--   Cone-Coeq {a} {b} f g = โ ฮป (x : X) -> โ ฮป (h : b โถ x) -> f โ h โฃ g โ h

-- module _ {๐ : Category ๐} where
  -- record hasLift {a b c : โจ ๐ โฉ} (f : b โถ c) (g : a โถ c) : ๐ฐ ๐ where
  --   field lift : a โถ b
  --         factors-lift : lift โ f โฃ g
  -- open hasLift public

-- = Unification

-- [Hide]
module _ {๐ : Category ๐} {{_ : hasCoproducts ๐}} {{_ : hasInitial ๐}} where
  data LeftOrRight {a b c : โจ ๐ โฉ} (f : a โถ b + c) : ๐ฐ ๐ where
    isRight         : (f~ : a โถ c) -> (f โฃ f~ โ ฮนโ) -> LeftOrRight f
    notAlwaysRight  : (x : โจ ๐ โฉ) -> (x โ ๐ -> ๐-๐ฐ) -> (xโ : x โถ b) -> (xโ : x โถ a)
                      -> (xโ โ ฮนโ โฃ xโ โ f) -> LeftOrRight f

  record isFinite (a : โจ ๐ โฉ) : ๐ฐ ๐ where
    field decideLoR : โ{b c : โจ ๐ โฉ} -> โ(f : Hom a (b + c)) -> LeftOrRight f

  open isFinite public
-- //

-- [Definition]
-- | Let [..] be a category with [..] and [..].
module _ (๐ : Category ๐) {{_ : hasCoproducts ๐}} {{_ : hasInitial ๐}} where
  -- |> We say that it has unification,
  record hasUnification : ๐ฐ ๐ where
  -- |> if for any two parallel arrows whose codomain is finite, the property of having a coequalizer is decidable.
  -- |  That is, there exists an algorithm:
    field unify : โ{a b : โจ ๐ โฉ} -> isFinite b -> โ(f g : a โถ b) -> Decision (hasCoequalizer f g)

                      -- -> (Cone-Coeq {{of ๐ โ T}} f g -> ๐-๐ฐ) +-๐ฐ (hasCoequalizer {{of ๐ โ T}} f g)

  open hasUnification public

  -- //

    -- module VUD-1 where
    --   module _ {a b c : โจ ๐ โฉ} where
    --     lem-1 : isFinite a -> isFinite b -> isFinite (a + b)
    --     hasLift-F (lem-1 P Q) f with hasLift-F P (ฮนโ โ f) | hasLift-F Q (ฮนโ โ f)
    --     ... | yes p | yes q =
    --       let f' = [ lift p , lift q ]

    --           Pโ : lift p โ map ฮนโ โฃ ฮนโ โ f
    --           Pโ = factors-lift p

    --           P : [ lift p , lift q ] โ map {{of โจ T โฉ}} ฮนโ โฃ f
    --           P = {!!}
    --       in yes (record { lift = f' ; factors-lift = P })
    --     ... | yes p | no ยฌp = {!!}
    --     ... | no ยฌp | Y = {!!}









