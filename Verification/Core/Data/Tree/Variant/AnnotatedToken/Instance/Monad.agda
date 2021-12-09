

module Verification.Core.Data.Tree.Variant.AnnotatedToken.Instance.Monad where

open import Verification.Conventions hiding (ℕ)

open import Verification.Core.Algebra.AllOf.Pointed
open import Verification.Core.Set.AllOf.Setoid
open import Verification.Core.Data.AllOf.Collection.Basics
open import Verification.Core.Category.Std.AllOf.Collection.Basics
open import Verification.Core.Category.Std.AllOf.Collection.Limits
open import Verification.Core.Category.Std.AllOf.Collection.Monads

open import Verification.Core.Theory.Std.Inference.Definition


open import Verification.Core.Data.Tree.Variant.AnnotatedToken.Data
open import Verification.Core.Data.Tree.Variant.AnnotatedToken.Definition



module _ {𝒹 : ATokenTreeData} {Ann : 𝐏𝐭𝐝₀} where
  map-ATokenTree : ∀{A B} -> (A -> B) -> ATokenTree 𝒹 Ann A -> ATokenTree 𝒹 Ann B
  map-ATokenTree = {!!}

  instance
    isFunctor:ATokenTree : isFunctor (𝐔𝐧𝐢𝐯 ℓ₀) (𝐔𝐧𝐢𝐯 ℓ₀) (ATokenTree 𝒹 Ann)
    isFunctor.map isFunctor:ATokenTree = map-ATokenTree
    isFunctor.isSetoidHom:map isFunctor:ATokenTree = {!!}
    isFunctor.functoriality-id isFunctor:ATokenTree = {!!}
    isFunctor.functoriality-◆ isFunctor:ATokenTree = {!!}

  instance
    isMonad:ATokenTree : isMonad (ATokenTree 𝒹 Ann)
    isMonad.pure isMonad:ATokenTree = {!!}
    isMonad.join isMonad:ATokenTree = {!!}
    isMonad.isNatural:pure isMonad:ATokenTree = {!!}
    isMonad.isNatural:join isMonad:ATokenTree = {!!}
    isMonad.unit-l-join isMonad:ATokenTree = {!!}
    isMonad.unit-r-join isMonad:ATokenTree = {!!}
    isMonad.assoc-join isMonad:ATokenTree = {!!}

ATokenTreeInfer : (d : ATokenTreeData) -> ∀ Ann -> 𝐈𝐧𝐟𝐞𝐫 _
ATokenTreeInfer 𝒹 Ann = incl (_ , ATokenTree 𝒹 Ann)
