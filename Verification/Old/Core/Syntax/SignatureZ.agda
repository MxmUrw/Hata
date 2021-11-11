
module Verification.Old.Core.Syntax.SignatureZ where

open import Verification.Conventions hiding (k)
open import Verification.Old.Core.Category
open import Verification.Old.Core.Order
open import Verification.Old.Core.Category.Monad
open import Verification.Old.Core.Category.Instance.Kleisli
open import Verification.Old.Core.Category.Instance.IdxSet
-- open import Verification.Unification.RecAccessible

module _ {K : 𝒰₀} where
  -- Symbol : 𝒰₀
  -- Symbol = ∑ λ (n : ℕ) -> K ×-𝒰 (Vec K n)

  Signature : 𝒰₁
  Signature = {n : ℕ} -> K -> Vec K (suc n) -> 𝒰₀

  data Term (σ : Signature) (V : K -> 𝒰₀) (k : K) : 𝒰₀
  data Terms (σ : Signature) (V : K -> 𝒰₀) : {n : ℕ} (ks : Vec K n) -> 𝒰₀ where
    [] : Terms σ V []
    _∷_ : ∀{k} {ks : Vec K n} -> Term σ V k -> Terms σ V ks -> Terms σ V (k ∷ ks)

  data Term σ V k where
    te : ∀{ks : Vec K (suc n)} -> σ k ks -> Terms σ V ks -> Term σ V k
    var : V k -> Term σ V k

  data TermsZ (σ : Signature) (V : K -> 𝒰₀) {n : ℕ} (ks : Vec K n) : 𝒰₀ where
    fail : TermsZ σ V ks
    valid : Terms σ V ks -> TermsZ σ V ks

  data TermZ (σ : Signature) (V : K -> 𝒰₀) (k : K) : 𝒰₀ where
    fail : TermZ σ V k
    valid : Term σ V k -> TermZ σ V k

  module _ {σ : Signature} {V : K -> 𝒰₀} where
    join-Term : {k : K} -> Term σ (TermZ σ V) k -> TermZ σ V k

    join-Terms : {ks : Vec K n} -> Terms σ (TermZ σ V) ks -> TermsZ σ V ks
    join-Terms [] = valid []
    join-Terms (t ∷ ts) with join-Term t | join-Terms ts
    ... | fail | ts' = fail
    ... | valid x | fail = fail
    ... | valid t' | valid ts' = valid (t' ∷ ts')

    join-Term (te t ts) with join-Terms ts
    ... | fail = fail
    ... | valid ts' = valid (te t ts')
    join-Term (var x) = x

    join-TermZ : {k : K} -> TermZ σ (TermZ σ V) k -> TermZ σ V k
    join-TermZ fail = fail
    join-TermZ (valid x) = join-Term x

  module _ {σ : Signature} {V W : K -> 𝒰₀} where
    map-Term : {k : K} -> (∀{k} -> V k -> W k) -> Term σ V k -> Term σ W k

    map-Terms : {ks : Vec K n} -> (∀{k} -> V k -> W k) -> Terms σ V ks -> Terms σ W ks
    map-Terms f [] = []
    map-Terms f (t ∷ ts) = map-Term f t ∷ map-Terms f ts

    map-Term f (te s ts) = te s (map-Terms f ts)
    map-Term f (var x) = var (f x)

    map-TermZ : {k : K} -> (∀{k} -> V k -> W k) -> TermZ σ V k -> TermZ σ W k
    map-TermZ f fail = fail
    map-TermZ f (valid x) = valid (map-Term f x)

  private
    𝒞 : Category _
    𝒞 = Category:IdxSet K ℓ₀

  module _ (σ : Signature) where
    Functor:TermZ : Functor 𝒞 𝒞
    ⟨ ⟨ Functor:TermZ ⟩ X ⟩ = TermZ σ ⟨ X ⟩
    IIdxSet.ISet:this (of ⟨ Functor:TermZ ⟩ z) = {!!}
    ⟨ IFunctor.map (of Functor:TermZ) f ⟩ = map-TermZ ⟨ f ⟩
    IFunctor.functoriality-id (of Functor:TermZ) = {!!}
    IFunctor.functoriality-◆ (of Functor:TermZ) = {!!}
    IFunctor.functoriality-≣ (of Functor:TermZ) = {!!}

    Monad:TermZ : Monad 𝒞
    ⟨ Monad:TermZ ⟩ = Functor:TermZ
    ⟨ IMonad.return (of Monad:TermZ) ⟩ x = valid (var x)
    ⟨ IMonad.join (of Monad:TermZ) ⟩ = join-TermZ
    IMonad.INatural:return (of Monad:TermZ) = {!!}
    IMonad.INatural:join (of Monad:TermZ) = {!!}
    IMonad.unit-l-join (of Monad:TermZ) = {!!}
    IMonad.unit-r-join (of Monad:TermZ) = {!!}
    IMonad.assoc-join (of Monad:TermZ) = {!!}





