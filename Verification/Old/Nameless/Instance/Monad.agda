
module Verification.Core.Data.Language.HindleyMilner.Variant.Unnamed.Typed.Instance.Monad where

open import Verification.Conventions hiding (ℕ ; _⊔_)
open import Verification.Core.Set.Discrete
open import Verification.Core.Algebra.Monoid.Definition
open import Verification.Core.Algebra.Monoid.Free
open import Verification.Core.Data.AllOf.Collection.Basics
open import Verification.Core.Data.AllOf.Collection.TermTools
open import Verification.Core.Category.Std.AllOf.Collection.Basics
open import Verification.Core.Category.Std.AllOf.Collection.Limits
open import Verification.Core.Category.Std.AllOf.Collection.Monads

open import Verification.Core.Theory.Std.Inference.Definition

open import Verification.Core.Theory.Std.Specific.ProductTheory.Module
open import Verification.Core.Theory.Std.Specific.ProductTheory.Instance.hasBoundaries

open import Verification.Core.Data.Language.HindleyMilner.Type.Definition
open import Verification.Core.Data.Language.HindleyMilner.Variant.Unnamed.Typed.Definition



map-TypedℒHM : ∀{A B : 𝐈𝐱 _ 𝐔𝐧𝐢𝐯₀} -> (A ⟶ B) -> TypedℒHM A ⟶ TypedℒHM B
map-TypedℒHM = {!!}

instance
  isFunctor:TypedℒHM : isFunctor (𝐈𝐱 _ (𝐔𝐧𝐢𝐯 ℓ₀)) (𝐈𝐱 _ (𝐔𝐧𝐢𝐯 ℓ₀)) (TypedℒHM)
  isFunctor.map isFunctor:TypedℒHM = map-TypedℒHM
  isFunctor.isSetoidHom:map isFunctor:TypedℒHM = {!!}
  isFunctor.functoriality-id isFunctor:TypedℒHM = {!!}
  isFunctor.functoriality-◆ isFunctor:TypedℒHM = {!!}

instance
  isMonad:TypedℒHM : isMonad (TypedℒHM)
  isMonad.pure isMonad:TypedℒHM = {!!}
  isMonad.join isMonad:TypedℒHM = {!!}
  isMonad.isNatural:pure isMonad:TypedℒHM = {!!}
  isMonad.isNatural:join isMonad:TypedℒHM = {!!}
  isMonad.unit-l-join isMonad:TypedℒHM = {!!}
  isMonad.unit-r-join isMonad:TypedℒHM = {!!}
  isMonad.assoc-join isMonad:TypedℒHM = {!!}

TypedℒHMInfer : 𝐈𝐧𝐟𝐞𝐫 _
TypedℒHMInfer = incl (_ , TypedℒHM)

