
module Verification.Core.Data.State.Definition where

open import Verification.Conventions
open import Verification.Core.Data.Product.Everything
open import Verification.Core.Data.Sum.Definition
open import Verification.Core.Data.Universe.Everything
open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Category.Std.Functor.Definition
open import Verification.Core.Category.Std.Monad.Definition
open import Verification.Core.Category.Std.Monad.TypeMonadNotation


module _ (T : Monad (𝐔𝐧𝐢𝐯 𝑖)) where
  record StateTᵘ (A : 𝒰 𝑖) (B : 𝒰 𝑖) : 𝒰 (𝑖) where
    constructor stateT
    field runStateT : A -> ⟨ T ⟩ (A × B)

  open StateTᵘ public

  module _ (A : 𝒰 𝑖) where
    macro StateT = #structureOn (StateTᵘ A)

module _ {T : Monad (𝐔𝐧𝐢𝐯 𝑖)} where
  private
    isFunctor:T : isFunctor (𝐔𝐧𝐢𝐯 𝑖) (𝐔𝐧𝐢𝐯 𝑖) ⟨ T ⟩
    isFunctor:T = it

  module _ {s : 𝒰 𝑖} where
    map-StateT : ∀{a b : 𝒰 𝑖} (f : a -> b) -> StateT T s a -> StateT T s b
    map-StateT f (stateT x) = stateT (map {{isFunctor:T}} (map (id , f)) ∘ x)

    instance
      isFunctor:StateT : isFunctor (𝐔𝐧𝐢𝐯 𝑖) (𝐔𝐧𝐢𝐯 𝑖) (StateT T s )
      isFunctor.map isFunctor:StateT = map-StateT
      isFunctor.isSetoidHom:map isFunctor:StateT = {!!}
      isFunctor.functoriality-id isFunctor:StateT = {!!}
      isFunctor.functoriality-◆ isFunctor:StateT = {!!}

    pure-StateT : ∀{a : 𝒰 𝑖} -> a -> StateT T s a
    pure-StateT a = stateT (λ s → pure (s , a))

    join-StateT : ∀{a : 𝒰 𝑖} -> StateT T s (StateT T s a) -> StateT T s a
    join-StateT (stateT f) = stateT (λ x → do x2 , (stateT f2) <- f x ; f2 x2)

    instance
      isMonad:StateT : isMonad (StateT T s)
      isMonad.pure isMonad:StateT = pure-StateT
      isMonad.join isMonad:StateT = join-StateT
      isMonad.isNatural:pure isMonad:StateT = {!!}
      isMonad.isNatural:join isMonad:StateT = {!!}
      isMonad.unit-l-join isMonad:StateT = {!!}
      isMonad.unit-r-join isMonad:StateT = {!!}
      isMonad.assoc-join isMonad:StateT = {!!}

    get : StateT T s s
    get = stateT (λ s → pure (s , s))

    put : ∀{b} -> b -> StateT T s b
    put b = stateT (λ s → pure (s , b))

    liftStateT : ∀{b} -> ⟨ T ⟩ b -> StateT T s b
    liftStateT b = stateT (λ s → do b <- b ; return (s , b))



