
module Verification.Core.Theory.Formal.Presentation.Signature.MultiSorted.Definition where

open import Verification.Conventions


Signature : (K : 𝒰₀) -> 𝒰 _
Signature K = {n : ℕ} -> K -> Vec K n -> 𝒰₀


module _ {K : 𝒰₀} where

  data Term (s : Signature K) (V : K -> 𝒰₀) (k : K) : 𝒰₀
  data Terms (σ : Signature K) (V : K -> 𝒰₀) : {n : ℕ} (ks : Vec K n) -> 𝒰₀ where
    [] : Terms σ V []
    _∷_ : ∀{k} {ks : Vec K n} -> Term σ V k -> Terms σ V ks -> Terms σ V (k ∷ ks)

  data Term σ V k where
    te : ∀{ks : Vec K n} -> σ k ks -> Terms σ V ks -> Term σ V k
    var : V k -> Term σ V k






