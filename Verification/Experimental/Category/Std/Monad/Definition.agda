
module Verification.Core.Category.Std.Monad.Definition where

open import Verification.Conventions

open import Verification.Core.Set.Setoid
open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Category.Std.Functor.Definition
open import Verification.Core.Category.Std.Functor.Instance.Category
open import Verification.Core.Category.Std.Natural.Definition
open import Verification.Core.Category.Std.Category.Instance.Category


-- module _ {𝒞 : Category 𝑖} where
--   record hasPure (F : Functor 𝒞 𝒞) : 𝒰 (⨆ 𝑖) where
--     field η : Natural ⟨ id ⟩ F
--     pure : ∀{a} -> a ⟶ ⟨ F ⟩ a
--     pure = ⟨ η ⟩



-- In this section we define monads.
-- | Let [..] be a category.
module _ {𝒞 : Category 𝑖} where
-- [Definition]
-- | A functor |F : 𝒞 ⟶ 𝒞| is a monad,
  record isMonad (F : Functor 𝒞 𝒞) : 𝒰 (⩏ 𝑖) where
    constructor monad
--  | if the following additional data is given:

-- | - Two maps |pure| and |join|:
    field pure  : ∀ A -> A ⟶ (⟨ F ⟩ A)
          join    : ∀ A -> (⟨ F ◆-𝐂𝐚𝐭 F ⟩ A) ⟶ (⟨ F ⟩ A)
-- | - Proofs that they are natural:
          {{isNatural:pure}}  : isNatural id (F) pure
          {{isNatural:join}}    : isNatural (F ◆-𝐂𝐚𝐭 F) (F) join
-- | - And behave monoidal.
          unit-l-join  : ∀{A : ⟨ 𝒞 ⟩} -> pure _ ◆ join _ ∼ id {a = ⟨ F ⟩ A}
          unit-r-join  : ∀{A : ⟨ 𝒞 ⟩} -> map (pure _) ◆ join _ ∼ id {a = ⟨ F ⟩ A}
          assoc-join   : ∀{A : ⟨ 𝒞 ⟩} -> join _ ◆ join _ ∼ (map (join _)) ◆ join A
  open isMonad {{...}} public
-- //


Monad : (𝒞 : Category 𝑖) -> 𝒰 _
Monad 𝒞 = Functor 𝒞 𝒞 :& isMonad

module _ {𝒞 : Category 𝑖} {T : ⟨ 𝒞 ⟩ -> ⟨ 𝒞 ⟩} {{_ : Monad 𝒞 on T}} where
  infixl 40 _>=>_
  _>=>_ : ∀{a b c : ⟨ 𝒞 ⟩} -> (a ⟶ T b) -> (b ⟶ T c) -> a ⟶ T c
  _>=>_ f g = f ◆ map g ◆ join _



-- unquoteDecl Monad monad = #struct "Mnd" (quote IMonad) "F" Monad monad








