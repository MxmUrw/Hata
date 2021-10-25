
module Verification.Experimental.Data.Expr.Variant.Base.InferenceTask where

open import Verification.Conventions hiding (lookup ; ℕ)

open import Verification.Experimental.Data.AllOf.Product
open import Verification.Experimental.Data.Expr.Variant.Base.Definition
open import Verification.Experimental.Data.Universe.Everything
open import Verification.Experimental.Category.Std.Category.Definition
open import Verification.Experimental.Category.Std.Category.Opposite
open import Verification.Experimental.Category.Std.Category.Construction.Product
open import Verification.Experimental.Category.Std.Category.Instance.FiniteProductCategory
open import Verification.Experimental.Category.Std.Limit.Specific.Product
open import Verification.Experimental.Category.Std.Limit.Specific.Product.Instance.Functor
open import Verification.Experimental.Category.Std.Functor.Definition
open import Verification.Experimental.Category.Std.Functor.Constant
open import Verification.Experimental.Set.Setoid.As.Category
open import Verification.Experimental.Set.Setoid.Discrete
open import Verification.Experimental.Set.Setoid.Definition

open import Verification.Experimental.Category.Std.Monad.Definition
open import Verification.Experimental.Category.Std.Monad.Instance.LargeCategory
open import Verification.Experimental.Theory.Std.Inference.Definition
open import Verification.Experimental.Theory.Std.Inference.TextInfer
open import Verification.Experimental.Theory.Std.Inference.Task
open import Verification.Experimental.Data.Expr.Variant.Base.Instance.Monad






BaseExprInferenceTask : BaseExprData -> InferenceTask _
BaseExprInferenceTask p = inferenceTask (BaseExprInfer p) (hasTextInfer:BaseExpr p) (BaseExprInfer p) id



