
module Verification.Experimental.Theory.Formal.Presentation.Signature.SingleSorted.Definition where

open import Verification.Experimental.Conventions


Signature : 𝒰 _
Signature = ℕ -> 𝒰₀


mutual
  data Terms (σ : Signature) (V : 𝒰 𝑖) : ℕ -> 𝒰 𝑖 where
    [] : Terms σ V 0
    _∷_ : Term σ V -> Terms σ V n -> Terms σ V (suc n)

  data Term (σ : Signature) (V : 𝒰 𝑖) : 𝒰 𝑖 where
    te : ∀{n} -> σ n -> Terms σ V n -> Term σ V
    var : V -> Term σ V


macro
  𝑇𝑒𝑟𝑚 : ∀ {𝑖} σ -> SomeStructure
  𝑇𝑒𝑟𝑚 {𝑖} σ = #structureOn (Term {𝑖} σ)






