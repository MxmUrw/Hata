
module Verification.Old.Core.Syntax.Signature where

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
  Signature = {n : ℕ} -> K -> Vec K n -> 𝒰₀

  data Term (s : Signature) (V : K -> 𝒰₀) (k : K) : 𝒰₀
  data Terms (σ : Signature) (V : K -> 𝒰₀) : {n : ℕ} (ks : Vec K n) -> 𝒰₀ where
    [] : Terms σ V []
    _∷_ : ∀{k} {ks : Vec K n} -> Term σ V k -> Terms σ V ks -> Terms σ V (k ∷ ks)

  data Term σ V k where
    te : ∀{ks : Vec K n} -> σ k ks -> Terms σ V ks -> Term σ V k
    var : V k -> Term σ V k

  data Term₊ (s : Signature) (V : Maybe K -> 𝒰₀) : (k : Maybe K) -> 𝒰₀ where
    none : Term₊ s V nothing
    some : ∀{k} -> Term s (λ k -> V (just k)) k -> Term₊ s V (just k)

  K₊ = Maybe K


  module _ {σ : Signature} where
    private
      variable k : K
               ks : Vec K n
               j : K₊

    join-Term : ∀{V : K -> 𝒰₀} -> Term σ (Term σ V) k -> Term σ V k

    join-Terms : ∀{V : K -> 𝒰₀} -> Terms σ (Term σ V) ks -> Terms σ V ks
    join-Terms [] = []
    join-Terms (t ∷ ts) = join-Term t ∷ join-Terms ts

    join-Term (te a ts) = te a (join-Terms ts)
    join-Term (var t) = t

    ⇈_ : (K₊ -> 𝒰₀) -> (K -> 𝒰₀)
    ⇈_ V k = V (just k)


    join-Term₊' : ∀{V : K₊ -> 𝒰₀} -> Term σ (⇈ Term₊ σ V) k -> Term σ (⇈ V) k

    join-Terms₊ : ∀{V : K₊ -> 𝒰₀} -> Terms σ (⇈ Term₊ σ V) ks -> Terms σ (⇈ V) ks
    join-Terms₊ [] = []
    join-Terms₊ (t ∷ ts) = join-Term₊' t ∷ join-Terms₊ ts

    join-Term₊' (te t ts) = te t (join-Terms₊ ts)
    join-Term₊' {k = k} (var (some x)) = x

    join-Term₊ : ∀{V : K₊ -> 𝒰₀} -> Term₊ σ (Term₊ σ V) j -> Term₊ σ V j
    join-Term₊ none = none
    join-Term₊ (some t) = some (join-Term₊' t)

    map-Term₊ : ∀{V W : K₊ -> 𝒰₀} -> (f : ∀ k -> V k -> W k) -> Term₊ σ V j -> Term₊ σ W j
    map-Term₊ f none = none
    map-Term₊ f (some (te x x₁)) = {!!}
    map-Term₊ f (some (var x)) = {!!}

{-

    private
      𝒞 : Category _
      𝒞 = ` IdxSet (Maybe K) ℓ₀ `

    Functor:Term : Functor 𝒞 𝒞
    ⟨ ⟨ Functor:Term ⟩ X ⟩ k = Term₊ σ ⟨ X ⟩ k
    of ⟨ Functor:Term ⟩ z = {!!}
    ⟨ IFunctor.map (of Functor:Term) f ⟩ k = map-Term₊ ⟨ f ⟩
    IFunctor.functoriality-id (of Functor:Term) = {!!}
    IFunctor.functoriality-◆ (of Functor:Term) = {!!}
    IFunctor.functoriality-≣ (of Functor:Term) = {!!}


    Monad:Term : Monad 𝒞
    ⟨ Monad:Term ⟩ = Functor:Term
    ⟨ IMonad.return (of Monad:Term) ⟩ nothing x = none
    ⟨ IMonad.return (of Monad:Term) ⟩ (just k) x = some (var x)
    ⟨ IMonad.join (of Monad:Term) ⟩ _ = join-Term₊
    IMonad.INatural:return (of Monad:Term) = {!!}
    IMonad.INatural:join (of Monad:Term) = {!!}
    IMonad.unit-l-join (of Monad:Term) = {!!}
    IMonad.unit-r-join (of Monad:Term) = {!!}
    IMonad.assoc-join (of Monad:Term) = {!!}

    data SigEdge : (a b : Maybe K) -> 𝒰₀ where
      e-arg : ∀ {k} {ks : Vec K n} -> (i : Fin-R n) -> σ k ks -> SigEdge (just (lookup i ks)) (just k)
      e-noarg : ∀{k} -> σ k [] -> SigEdge nothing (just k)

    𝑄 : Quiver ⊥
    ⟨ 𝑄 ⟩ = Maybe K
    IQuiver.Edge (of 𝑄) = SigEdge
    IQuiver._≈_ (of 𝑄) = _≡_
    IQuiver.IEquivInst (of 𝑄) = IEquiv:Path


    decomp : ∀{V : K₊ -> 𝒰₀} (k : K₊) -> Term₊ σ V k -> V k +-𝒰 (∀(j : K₊) -> SigEdge j k -> Maybe (Term₊ σ V j))
    decomp nothing none = right (λ j ())
    decomp {V = V} (just k) (some (te t ts)) = right (f ts)
      where f : Terms σ (⇈ V) ks -> (j : K₊) -> SigEdge j (just k) -> Maybe (Term₊ σ _ j)
            f xs .(just (lookup i _)) (e-arg i x) = {!!}
            f xs .nothing (e-noarg x) = {!!}
            -- f .(just (lookup i _)) (e-arg i x) = {!!}
            -- f .nothing (e-noarg x) = {!!}
    decomp (just k) (some (var v)) = left v

    -- RecAccessible:Term : IRecAccessible Monad:Term
    -- IRecAccessible.Dir RecAccessible:Term = of 𝑄
    -- IRecAccessible.ISet:Dir RecAccessible:Term = {!!}
    -- ⟨ ⟨ IRecAccessible.decompose RecAccessible:Term ⟩ ⟩ = decomp
    -- of IRecAccessible.decompose RecAccessible:Term = {!!}
    -- IRecAccessible.IMono:decompose RecAccessible:Term = {!!}
    -- IRecAccessible.wellfounded RecAccessible:Term = {!!}

{-

  -- 𝑄 : Signature n -> Quiver ⊥
  -- ⟨ 𝑄 {n} s ⟩ = K
  -- IQuiver.Edge (of 𝑄 s) = {!!}
  -- IQuiver._≈_ (of 𝑄 s) = {!!}
  -- IQuiver.IEquivInst (of 𝑄 s) = {!!}





-}
-}


