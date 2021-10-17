
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

-- module _ {X : 𝒰 𝑖} {{_ : ICategory X 𝑗}} where
--   Cone-Coeq : ∀{a b : X} -> (f g : a ⟶ b) -> 𝒰 _
--   Cone-Coeq {a} {b} f g = ∑ λ (x : X) -> ∑ λ (h : b ⟶ x) -> f ◆ h ≣ g ◆ h

-- module _ {𝒞 : Category 𝑖} where
  -- record hasLift {a b c : ⟨ 𝒞 ⟩} (f : b ⟶ c) (g : a ⟶ c) : 𝒰 𝑖 where
  --   field lift : a ⟶ b
  --         factors-lift : lift ◆ f ≣ g
  -- open hasLift public

-- = Unification

-- [Hide]
module _ {𝒞 : Category 𝑖} {{_ : hasCoproducts 𝒞}} {{_ : hasInitial 𝒞}} where
  data LeftOrRight {a b c : ⟨ 𝒞 ⟩} (f : a ⟶ b + c) : 𝒰 𝑖 where
    isRight         : (f~ : a ⟶ c) -> (f ≣ f~ ◆ ι₁) -> LeftOrRight f
    notAlwaysRight  : (x : ⟨ 𝒞 ⟩) -> (x ≅ 𝟘 -> 𝟘-𝒰) -> (x₀ : x ⟶ b) -> (x₁ : x ⟶ a)
                      -> (x₀ ◆ ι₀ ≣ x₁ ◆ f) -> LeftOrRight f

  record isFinite (a : ⟨ 𝒞 ⟩) : 𝒰 𝑖 where
    field decideLoR : ∀{b c : ⟨ 𝒞 ⟩} -> ∀(f : Hom a (b + c)) -> LeftOrRight f

  open isFinite public
-- //

-- [Definition]
-- | Let [..] be a category with [..] and [..].
module _ (𝒞 : Category 𝑖) {{_ : hasCoproducts 𝒞}} {{_ : hasInitial 𝒞}} where
  -- |> We say that it has unification,
  record hasUnification : 𝒰 𝑖 where
  -- |> if for any two parallel arrows whose codomain is finite, the property of having a coequalizer is decidable.
  -- |  That is, there exists an algorithm:
    field unify : ∀{a b : ⟨ 𝒞 ⟩} -> isFinite b -> ∀(f g : a ⟶ b) -> Decision (hasCoequalizer f g)

                      -- -> (Cone-Coeq {{of 𝒞 ⌄ T}} f g -> 𝟘-𝒰) +-𝒰 (hasCoequalizer {{of 𝒞 ⌄ T}} f g)

  open hasUnification public

  -- //

    -- module VUD-1 where
    --   module _ {a b c : ⟨ 𝒞 ⟩} where
    --     lem-1 : isFinite a -> isFinite b -> isFinite (a + b)
    --     hasLift-F (lem-1 P Q) f with hasLift-F P (ι₀ ◆ f) | hasLift-F Q (ι₁ ◆ f)
    --     ... | yes p | yes q =
    --       let f' = [ lift p , lift q ]

    --           P₀ : lift p ◆ map ι₁ ≣ ι₀ ◆ f
    --           P₀ = factors-lift p

    --           P : [ lift p , lift q ] ◆ map {{of ⟨ T ⟩}} ι₁ ≣ f
    --           P = {!!}
    --       in yes (record { lift = f' ; factors-lift = P })
    --     ... | yes p | no ¬p = {!!}
    --     ... | no ¬p | Y = {!!}









