
module Verification.Core.Data.Expr.Variant.Base.InferenceTask where

open import Verification.Conventions hiding (lookup ; ℕ)

open import Verification.Core.Data.AllOf.Product
open import Verification.Core.Data.Expr.Variant.Base.Definition
open import Verification.Core.Data.Universe.Everything
open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Category.Std.Category.Opposite
open import Verification.Core.Category.Std.Category.Construction.Product
open import Verification.Core.Category.Std.Category.Instance.FiniteProductCategory
open import Verification.Core.Category.Std.Limit.Specific.Product
open import Verification.Core.Category.Std.Limit.Specific.Product.Instance.Functor
open import Verification.Core.Category.Std.Functor.Definition
open import Verification.Core.Category.Std.Functor.Constant
open import Verification.Core.Set.Setoid.As.Category
open import Verification.Core.Set.Setoid.Discrete
open import Verification.Core.Set.Setoid.Definition

open import Verification.Core.Category.Std.Monad.Definition
open import Verification.Core.Category.Std.Monad.Instance.LargeCategory
open import Verification.Core.Theory.Std.Inference.Definition
open import Verification.Core.Theory.Std.Inference.TextInfer
open import Verification.Core.Theory.Std.Inference.Task
open import Verification.Core.Data.Expr.Variant.Base.Instance.Monad





{-

BaseExprInferenceTask : BaseExprData -> InferenceTask _
BaseExprInferenceTask p = inferenceTask (BaseExprInfer p) (hasTextInfer:BaseExpr p) (BaseExprInfer p) id

-}

