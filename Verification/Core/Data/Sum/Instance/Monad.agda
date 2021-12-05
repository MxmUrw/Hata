
module Verification.Core.Data.Sum.Instance.Monad where

open import Verification.Conventions
open import Verification.Core.Set.Function.Injective
open import Verification.Core.Set.Setoid
open import Verification.Core.Data.Sum.Definition
open import Verification.Core.Data.Product.Definition
open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Category.Std.Functor.Definition
open import Verification.Core.Category.Std.Functor.Instance.Category
open import Verification.Core.Category.Std.Monad.Definition
open import Verification.Core.Category.Std.Monad.KleisliCategory.Instance.Monoidal
open import Verification.Core.Category.Std.Monad.TypeMonadNotation
open import Verification.Core.Data.Universe.Definition
open import Verification.Core.Data.Universe.Instance.Category
open import Verification.Core.Data.Universe.Instance.Monoidal
open import Verification.Core.Data.Sum.Instance.Functor



module _ {A : 𝒰 𝑖} where
  instance
    isMonad:+⧿ : isMonad {𝒞 = 𝐓𝐲𝐩𝐞 𝑖} (A +⧿)
    isMonad:+⧿ = monad pure-+ join-+ {{{!!}}} {{{!!}}} {!!} {!!} {!!}

      where
        pure-+ : ∀(B : 𝒰 𝑖) -> (B ⟶ A + B)
        pure-+ _ = right

        join-+ : ∀(B : 𝒰 𝑖) -> (A +-𝒰 (A + B)) ⟶ (A + B)
        join-+ _ = (either left idf)

instance
  isLaxMonoidalFunctor:Maybe : isLaxMonoidalFunctor {𝒞 = 𝐔𝐧𝐢𝐯 𝑖} {𝒟 = 𝐔𝐧𝐢𝐯 𝑖} (⊤-𝒰 {𝑖} +⧿)
  isLaxMonoidalFunctor.lax-unit isLaxMonoidalFunctor:Maybe = right
  isLaxMonoidalFunctor.lax-mult isLaxMonoidalFunctor:Maybe = λ (a , b) -> do a' <- a
                                                                             b' <- b
                                                                             return (a' , b')
  -- isLaxMonoidalFunctor.lax-unit-l isLaxMonoidalFunctor:Maybe i (fst₁ , left x) = left x
  -- isLaxMonoidalFunctor.lax-unit-l isLaxMonoidalFunctor:Maybe i (fst₁ , just x) = just x

instance
  isMonoidalMonad:Maybe : isMonoidalMonad {𝒞 = 𝐔𝐧𝐢𝐯 𝑖} (⊤-𝒰 {𝑖} +⧿)
  isMonoidalMonad.isLaxMonoidalFunctor:this isMonoidalMonad:Maybe = isLaxMonoidalFunctor:Maybe
  isMonoidalMonad.compat-lax-unit isMonoidalMonad:Maybe = refl-≡
  -- isMonoidalMonad.compat-lax-mult isMonoidalMonad:Maybe = refl-≡



