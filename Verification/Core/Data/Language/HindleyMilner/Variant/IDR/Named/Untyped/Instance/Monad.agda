
module Verification.Core.Data.Language.HindleyMilner.Variant.Untyped.Instance.Monad where

open import Verification.Conventions hiding (ℕ)
open import Verification.Core.Set.Discrete
open import Verification.Core.Algebra.Monoid.Definition
open import Verification.Core.Algebra.Monoid.Free
open import Verification.Core.Data.AllOf.Product
open import Verification.Core.Data.AllOf.Sum
open import Verification.Core.Data.AllOf.Nat
open import Verification.Core.Data.AllOf.Universe
open import Verification.Core.Data.AllOf.Substitution
open import Verification.Core.Data.Indexed.Definition

open import Verification.Core.Category.Std.Monad.Definition
open import Verification.Core.Category.Std.Monad.Instance.Category
open import Verification.Core.Category.Std.Monad.Instance.LargeCategory
open import Verification.Core.Theory.Std.Inference.Definition

open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Category.Std.Category.Opposite
open import Verification.Core.Category.Std.Category.Construction.Product
open import Verification.Core.Category.Std.Category.Instance.FiniteProductCategory
open import Verification.Core.Category.Std.Limit.Specific.Product
open import Verification.Core.Category.Std.Limit.Specific.Product.Instance.Functor
open import Verification.Core.Category.Std.Functor.Definition
open import Verification.Core.Category.Std.Functor.Constant

open import Verification.Core.Theory.Std.Specific.ProductTheory.Module
open import Verification.Core.Theory.Std.Specific.ProductTheory.Instance.hasBoundaries

open import Verification.Core.Data.Language.HindleyMilner.Variant.Untyped.Definition



map-UntypedℒHM : ∀{A B : 𝐈𝐱 _ 𝐔𝐧𝐢𝐯₀} -> (A ⟶ B) -> UntypedℒHM A ⟶ UntypedℒHM B
map-UntypedℒHM = {!!}

instance
  isFunctor:UntypedℒHM : isFunctor (𝐈𝐱 _ (𝐔𝐧𝐢𝐯 ℓ₀)) (𝐈𝐱 _ (𝐔𝐧𝐢𝐯 ℓ₀)) (UntypedℒHM)
  isFunctor.map isFunctor:UntypedℒHM = map-UntypedℒHM
  isFunctor.isSetoidHom:map isFunctor:UntypedℒHM = {!!}
  isFunctor.functoriality-id isFunctor:UntypedℒHM = {!!}
  isFunctor.functoriality-◆ isFunctor:UntypedℒHM = {!!}

instance
  isMonad:UntypedℒHM : isMonad (UntypedℒHM)
  isMonad.pure isMonad:UntypedℒHM = {!!}
  isMonad.join isMonad:UntypedℒHM = {!!}
  isMonad.isNatural:pure isMonad:UntypedℒHM = {!!}
  isMonad.isNatural:join isMonad:UntypedℒHM = {!!}
  isMonad.unit-l-join isMonad:UntypedℒHM = {!!}
  isMonad.unit-r-join isMonad:UntypedℒHM = {!!}
  isMonad.assoc-join isMonad:UntypedℒHM = {!!}

UntypedℒHMInfer : 𝐈𝐧𝐟𝐞𝐫 _
UntypedℒHMInfer = incl (_ , UntypedℒHM)



