
module Verification.Experimental.Theory.Std.Inference.TextInfer where

open import Verification.Conventions hiding (lookup ; ℕ)



open import Verification.Experimental.Data.Nat.Free
open import Verification.Experimental.Data.Universe.Everything
open import Verification.Experimental.Category.Std.Category.Definition
open import Verification.Experimental.Category.Std.Category.Opposite
open import Verification.Experimental.Category.Std.Functor.Definition

open import Verification.Experimental.Category.Std.Monad.Definition
open import Verification.Experimental.Category.Std.RelativeMonad.Finitary.Definition
-- open import Verification.Experimental.Category.Std.Monad.KleisliCategory.Instance.Monoidal
open import Verification.Experimental.Category.Std.Monad.TypeMonadNotation
open import Verification.Experimental.Data.AllOf.Sum
open import Verification.Experimental.Data.Substitution.Definition
open import Verification.Experimental.Data.Indexed.Definition
open import Verification.Experimental.Data.Indexed.Instance.Monoid
open import Verification.Experimental.Data.FiniteIndexed.Definition

open import Verification.Experimental.Algebra.Monoid.Free
open import Verification.Experimental.Algebra.Monoid.Free.Element
open import Verification.Experimental.Category.Std.Category.Subcategory.Full
open import Verification.Experimental.Category.Std.Category.Instance.Category
open import Verification.Experimental.Category.Std.Limit.Specific.Coproduct.Definition

open import Verification.Experimental.Theory.Std.Inference.Definition


record hasTextInfer (TIMonad : Monad (𝐔𝐧𝐢𝐯 𝑖)) : 𝒰 (𝑖 ⁺) where
  field TIObj : 𝒰 𝑖
  field parse : Text -> Text + ⟨ TIMonad ⟩ TIObj
  field {{IShow:TI}} : IShow (⟨ TIMonad ⟩ TIObj)



