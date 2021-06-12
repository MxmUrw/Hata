
module Verification.Experimental.Theory.Presentation.Signature.SingleSorted.Instance.Setoid where

open import Verification.Conventions

open import Verification.Experimental.Set.Setoid
open import Verification.Experimental.Theory.Presentation.Signature.SingleSorted.Definition
-- open import Verification.Experimental.Category.Std.Category.Definition
-- open import Verification.Experimental.Category.Std.Functor.Definition
-- open import Verification.Experimental.Category.Std.Monad.Definition


module _ {σ : Signature} {V : 𝒰 𝑗} {{_ : isSetoid 𝑖 V}} where

  mutual
    data _∼-Term_ : Term σ V -> Term σ V -> 𝒰 (𝑗 ､ 𝑖) where
      var : ∀{v w : V} -> v ∼ w -> var v ∼-Term var w
      te : ∀{a : σ n} {xs ys : Terms σ V n} -> (xs ∼-Terms ys) -> te a xs ∼-Term te a ys

    data _∼-Terms_ : Terms σ V n -> Terms σ V n -> 𝒰 (𝑗 ､ 𝑖) where
      [] : [] ∼-Terms []
      _∷_ : ∀{t s : Term σ V} -> {xs ys : Terms σ V n} -> (t ∼-Term s) -> (xs ∼-Terms ys) -> ((t ∷ xs) ∼-Terms (s ∷ ys))


  instance
    mutual
      isEquivRel:∼-Term : isEquivRel (∼-Base _∼-Term_)
      isEquivRel.refl isEquivRel:∼-Term {te x x₁} = incl (te {!!})
      isEquivRel.refl isEquivRel:∼-Term {var x} = incl (var refl)
      isEquivRel.sym isEquivRel:∼-Term = {!!}
      isEquivRel._∙_ isEquivRel:∼-Term = {!!}

      isEquivRel:∼-Terms : ∀{n} -> isEquivRel (∼-Base (_∼-Terms_ {n}))
      isEquivRel:∼-Terms = {!!}

  instance
    isSetoid:Term : isSetoid _ (Term σ V)
    isSetoid._∼'_ isSetoid:Term = _∼-Term_
    isSetoid.isEquivRel:∼ isSetoid:Term = it







