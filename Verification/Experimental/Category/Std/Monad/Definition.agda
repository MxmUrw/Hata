
module Verification.Experimental.Category.Std.Monad.Definition where

open import Verification.Conventions

open import Verification.Experimental.Set.Setoid
open import Verification.Experimental.Category.Std.Category.Definition
open import Verification.Experimental.Category.Std.Functor.Definition
open import Verification.Experimental.Category.Std.Functor.Instance.Category
open import Verification.Experimental.Category.Std.Natural.Definition
open import Verification.Experimental.Category.Std.Category.Instance.Category


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
  record isMonad (F : Functor 𝒞 𝒞) : 𝒰 (⨆ 𝑖) where
--  | if the following additional data is given:

-- | - Two maps |pure| and |join|:
    field pure  : ∀{A} -> A ⟶ (⟨ F ⟩ A)
          join    : ∀{A} -> (⟨ F ◆-Cat F ⟩ A) ⟶ (⟨ F ⟩ A)
-- | - Proofs that they are natural:
          {{isNatural:pure}}  : isNatural ⟨ id ⟩ (F) pure
          {{isNatural:join}}    : isNatural (F ◆-Cat F) (F) join
-- | - And behave monoidal.
          unit-l-join  : ∀{A : ⟨ 𝒞 ⟩} -> pure ◆ join ∼ id {a = ⟨ F ⟩ A}
          unit-r-join  : ∀{A : ⟨ 𝒞 ⟩} -> map pure ◆ join ∼ id {a = ⟨ F ⟩ A}
          assoc-join   : ∀{A : ⟨ 𝒞 ⟩} -> join ◆ join ∼ (map join) ◆ join {A = A}
  open isMonad {{...}} public
-- //


Monad : (𝒞 : Category 𝑖) -> 𝒰 _
Monad 𝒞 = Functor 𝒞 𝒞 :& isMonad

-- unquoteDecl Monad monad = #struct "Mnd" (quote IMonad) "F" Monad monad








