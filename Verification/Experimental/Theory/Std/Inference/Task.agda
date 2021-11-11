
module Verification.Experimental.Theory.Std.Inference.Task where

open import Verification.Conventions hiding (lookup ; ℕ)


open import Verification.Experimental.Set.Setoid.Definition
open import Verification.Experimental.Set.Setoid.Instance.Category
open import Verification.Experimental.Data.Nat.Free
open import Verification.Experimental.Data.Universe.Everything
open import Verification.Experimental.Category.Std.Category.Definition
open import Verification.Experimental.Category.Std.Category.Opposite
open import Verification.Experimental.Category.Std.Functor.Definition
open import Verification.Experimental.Category.Std.Morphism.Iso

open import Verification.Experimental.Category.Std.Monad.Definition
open import Verification.Experimental.Category.Std.Monad.Instance.LargeCategory
open import Verification.Experimental.Category.Std.RelativeMonad.Finitary.Definition
-- open import Verification.Experimental.Category.Std.Monad.KleisliCategory.Instance.Monoidal
open import Verification.Experimental.Category.Std.Monad.TypeMonadNotation
open import Verification.Experimental.Data.Substitution.Variant.Base.Definition
open import Verification.Experimental.Data.Indexed.Definition
open import Verification.Experimental.Data.Indexed.Instance.Monoid
open import Verification.Experimental.Data.FiniteIndexed.Definition

open import Verification.Experimental.Algebra.Monoid.Free
open import Verification.Experimental.Algebra.Monoid.Free.Element
open import Verification.Experimental.Category.Std.Category.Subcategory.Full
open import Verification.Experimental.Category.Std.Category.Instance.Category
open import Verification.Experimental.Category.Std.Limit.Specific.Coproduct.Definition
open import Verification.Experimental.Category.Std.Category.Subcategory.Definition

open import Verification.Experimental.Theory.Std.Inference.Definition
open import Verification.Experimental.Theory.Std.Inference.TextInfer

-- record InferenceTask (𝑖 : 𝔏 ^ 4) : 𝒰 (𝑖 ⁺ ⁺) where
  -- constructor inferenceTask
  -- field Start : Monad (𝐔𝐧𝐢𝐯 (𝑖 ⌄ 0))
  -- field hasTextInfer:Start : hasTextInfer Start
  -- field Target : 𝐈𝐧𝐟𝐞𝐫 _ -- (𝑖 ⌄ 1 ⋯ 3)
  -- field inference : incl (_ , Start) ⟶ Target


record InferenceTask (𝑖 : 𝔏 ^ 3) : 𝒰 (𝑖 ⁺ ⁺) where
  constructor inferenceTask
  field Start : 𝐈𝐧𝐟𝐞𝐫 𝑖
  field hasTextInfer:Start : hasTextInfer Start
  field Target : 𝐈𝐧𝐟𝐞𝐫 𝑖 -- (𝑖 ⌄ 1 ⋯ 3)
  field inference : Target ⟶ Start


executeInferenceFlat : InferenceTask 𝑖 -> Text -> Text
executeInferenceFlat (inferenceTask Start TI Target inference) input =
  case (parse TI input) of
    id-𝒰
    λ val -> let myf = ⟨ ⟨ rep TI ⟩⁻¹ ⟩ val
                 myg = runaround inference
                 myf' = myf ◆ ⟨ myg ⟩ _
              in show $ ⟨ ⟨ rep TI ⟩ ⟩ myf'



