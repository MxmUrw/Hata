
module Verification.Core.Data.Language.HindleyMilner.Variant.Unnamed.Untyped.Instance.Monad where

open import Verification.Conventions hiding (ℕ)
open import Verification.Core.Set.Discrete
open import Verification.Core.Algebra.Monoid.Definition
open import Verification.Core.Algebra.Monoid.Free
open import Verification.Core.Data.AllOf.Collection.Basics
open import Verification.Core.Data.AllOf.Collection.TermTools
open import Verification.Core.Category.Std.AllOf.Collection.Basics
open import Verification.Core.Category.Std.AllOf.Collection.Limits
open import Verification.Core.Category.Std.AllOf.Collection.Monads

open import Verification.Core.Theory.Std.Inference.Definition

open import Verification.Core.Data.Language.HindleyMilner.Variant.Unnamed.Untyped.Definition



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


