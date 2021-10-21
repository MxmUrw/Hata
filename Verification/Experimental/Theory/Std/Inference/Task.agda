
module Verification.Experimental.Theory.Std.Inference.Task where

open import Verification.Conventions hiding (lookup ; ℕ)


open import Verification.Experimental.Data.Nat.Free
open import Verification.Experimental.Data.Universe.Everything
open import Verification.Experimental.Category.Std.Category.Definition
open import Verification.Experimental.Category.Std.Category.Opposite
open import Verification.Experimental.Category.Std.Functor.Definition

open import Verification.Experimental.Category.Std.Monad.Definition
open import Verification.Experimental.Category.Std.Monad.Instance.Category
open import Verification.Experimental.Category.Std.RelativeMonad.Finitary.Definition
-- open import Verification.Experimental.Category.Std.Monad.KleisliCategory.Instance.Monoidal
open import Verification.Experimental.Category.Std.Monad.TypeMonadNotation
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
open import Verification.Experimental.Theory.Std.Inference.TextInfer


record InferenceTask (𝑖 : 𝔏 ^ 4) : 𝒰 (𝑖 ⁺) where
  constructor inferenceTask
  field Start : Monad (𝐔𝐧𝐢𝐯 (𝑖 ⌄ 0))
  field hasTextInfer:Start : hasTextInfer Start
  field Target : 大𝐌𝐧𝐝 (𝑖 ⌄ 1 ⋯ 3)
  field inference : 大MonadHom (_ , Start) Target


executeInferenceFlat : InferenceTask 𝑖 -> Text -> Text
executeInferenceFlat (inferenceTask Start hasTextInfer:Start Target inference) = {!!}



