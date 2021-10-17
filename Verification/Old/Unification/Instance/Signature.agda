
module Verification.Unification.Instance.Signature where

open import Verification.Conventions hiding (k)
open import Verification.Core.Category
open import Verification.Core.Order
open import Verification.Core.Type
open import Verification.Core.Category.Monad
open import Verification.Core.Category.Instance.Kleisli
open import Verification.Core.Category.Instance.IdxSet
open import Verification.Unification.RecAccessible

open import Verification.Core.Syntax.SignatureZ

instance
  IDiscreteStr:Vec : ∀{A : 𝒰 𝑖} {{_ : IDiscreteStr A}} -> IDiscreteStr (Vec A n)
  (IDiscreteStr:Vec IDiscreteStr.≟-Str a) b = {!!}

  IDiscreteStr:ℕ : IDiscreteStr ℕ
  IDiscreteStr:ℕ = {!!}


module _ {K : 𝒰₀} {{_ : IDiscreteStr K}} where

  module _ {σ : Signature} where
    private
      variable k : K
               ks : Vec K n
               -- j : K

    module _ {{_ : ∀{n k} {ks : Vec K (suc n)} -> IDiscreteStr (σ k ks)}} where

    -- private
    --   𝒞 : Category _
    --   𝒞 = ` IdxSet (Maybe K) ℓ₀ `

    -- data SigEdge : (a b : Maybe K) -> 𝒰₀ where
    --   e-arg : ∀ {k} {ks : Vec K (suc n)} -> (i : Fin-R n) -> σ k ks -> SigEdge (just (lookup i ks)) (just k)
    --   e-noarg : ∀{k} -> σ k [] -> SigEdge nothing (just k)

      data SigEdge : (a b : K) -> 𝒰₀ where
        edge : ∀ {k} {ks : Vec K (suc n)} -> (i : Fin-R (suc n)) -> σ k ks -> SigEdge (lookup i ks) k
        fail : ∀{a : K} -> SigEdge a a

      𝑄 : Quiver ⊥
      ⟨ 𝑄 ⟩ = K
      IQuiver.Edge (of 𝑄) = SigEdge
      IQuiver._≈_ (of 𝑄) = _≡_
      IQuiver.IEquivInst (of 𝑄) = IEquiv:Path

      -- compare-sig : ∀{k j₁ j₂ : K} -> {n₁ n₂ : ℕ} -> (s )

      module _ {V : K -> 𝒰₀} where
        lookup-Term : ∀{ks : Vec K (n)} -> (i : Fin-R (n)) -> Terms σ V ks -> Term σ V (lookup i ks)
        lookup-Term zero    (t ∷ ts) = t
        lookup-Term (suc i) (t ∷ ts) = lookup-Term i ts

        lookup-Term-try : ∀{n₁ n₂ : ℕ} {ks₁ : Vec K (suc n₁)} {ks₂ : Vec K (suc n₂)} (s₁ : σ k ks₁) (s₂ : σ k ks₂) (i : Fin-R (suc n₂)) (ts : Terms σ V ks₁) -> Maybe (TermZ σ V (lookup i ks₂))
        lookup-Term-try {n₁ = n₁} {n₂} {ks₁} {ks₂} s₁ s₂ i ts with (n₁ ≟-Str n₂)
        ... | no ¬p = nothing
        ... | yes refl-StrId with (ks₁ ≟-Str ks₂)
        ... | no ¬p = nothing
        ... | yes refl-StrId with (s₁ ≟-Str s₂)
        ... | no ¬p = nothing
        ... | yes refl-StrId = right (valid (lookup-Term i ts))

      module _ {X Y : K -> 𝒰₀} where
        naturality-lookup-Term : (f : ∀{k} -> X k -> Y k) -> ∀{ks : Vec K (n)} -> (i : Fin-R (n)) -> (ts : Terms σ X ks) -> (map-Term f (lookup-Term i ts)) ≡ (lookup-Term i (map-Terms f ts))
        naturality-lookup-Term f zero (t ∷ ts) = refl
        naturality-lookup-Term f (suc i) (t ∷ ts) = naturality-lookup-Term f i ts

        naturality-lookup-Term-try : (f : ∀{k} -> X k -> Y k) {k : K} -> ∀ {n n₁}
                                     -> ∀ {ks₁ : Vec K (suc n)} {ks₂ : Vec K (suc n₁)} ->
                            -- (t : TermZ σ X k) →
                            (s₁ : σ k ks₁) ->
                            (s₂ : σ k ks₂) ->
                            (ts  : Terms σ X ks₁) →
                            (i : Fin-R (suc n₁)) ->
                            map-Maybe (map-TermZ f) (lookup-Term-try s₁ s₂ i ts) ≡
                                  lookup-Term-try s₁ s₂ i (map-Terms f ts)
        naturality-lookup-Term-try f {k} {n} {n₁} {ks₁} {ks₂} s₁ s₂ ts i with (n ≟-Str n₁)
        ... | no ¬p = refl
        ... | yes refl-StrId with (ks₁ ≟-Str ks₂)
        ... | no ¬p = refl
        ... | yes refl-StrId with (s₁ ≟-Str s₂)
        ... | no ¬p = refl
        ... | yes refl-StrId = λ j -> just (valid (naturality-lookup-Term f i ts j))

      -- [Theorem]
      -- | The |Monad:TermZ| is recursively accessible.
      interleaved mutual
        RecAccessible:TermZ : IRecAccessible (Monad:TermZ σ)

        -- | First we build the decomposition function:
        decomp : {k : K} {V : K -> 𝒰₀} -> TermZ σ V k -> (∀{j : K} -> SigEdge j k -> Maybe (TermZ σ V j))
        decomp _ fail = right fail
        decomp fail (edge _ _) = right fail
        decomp (valid (var x)) (edge _ _) = nothing
        decomp (valid (te s₁ ts)) (edge i s₂) = lookup-Term-try s₁ s₂ i ts

        module _ {X Y : K -> 𝒰₀} where
          naturality-decomp : (f : ∀{k} -> X k -> Y k) {k : K}
                              (t : TermZ σ X k) →
                              ∀{j} -> (e : SigEdge j k) ->
                              map-Maybe (map-TermZ f) (decomp t e) ≡ decomp (map-TermZ f t) e
          naturality-decomp f t fail = refl
          naturality-decomp f fail (edge i x) = refl
          naturality-decomp f (valid (te s₁ ts)) (edge i s₂) = naturality-lookup-Term-try f s₁ s₂ ts i
          naturality-decomp f (valid (var x₁)) (edge i x) = refl

        module lem-20 {X : K -> 𝒰₀} where
          proof : (t : TermZ σ (TermZ σ X) k) →
                  ∀{j} -> (e : SigEdge j k) ->
                  map-Maybe join-TermZ (decomp t e) ≡ decomp (join-TermZ t) e
          proof t fail = refl
          proof fail (edge i x) = refl
          proof (valid (te x₁ x₂)) (edge i x) = {!!}
          proof (valid (var fail)) (edge i x) = {!!}
          proof (valid (var (valid x₁))) (edge i x) = {!!}

        module lem-25 {X Y : K -> 𝒰₀} (f : ∀{k} -> X k -> TermZ σ Y k) where
          interleaved mutual
            proof : ∀{j k} -> ∀(e : Edge {{of 𝑄}} k j) -> ∀ t -> (decomp t e ≢ nothing) -> map-Maybe (λ a → join-TermZ (map-TermZ f a)) (decomp t e)
                    ≡ decomp (join-TermZ (map-TermZ f t)) e

            P0 :  {k : K} -> ∀ {n n₁} -> ∀ {ks₁ : Vec K (suc n)} {ks₂ : Vec K (suc n₁)} ->
                              -- (t : TermZ σ X k) →
                              (s₁ : σ k ks₁) ->
                              (s₂ : σ k ks₂) ->
                              (ts  : Terms σ X ks₁) →
                              (i : Fin-R (suc n₁)) ->
                              -- (decomp t e ≢ nothing) ->
                              (lookup-Term-try s₁ s₂ i ts ≢ nothing) ->
                              map-Maybe (λ a -> join-TermZ (map-TermZ f a)) (lookup-Term-try s₁ s₂ i ts) ≡
                                    decomp (join-Term (te s₁ (map-Terms f ts))) (edge i s₂)
                                    -- lookup-Term-try s₁ s₂ i (map-Terms f ts)
            P0 {k} {n₁} {n₂} {ks₁} {ks₂} s₁ s₂ ts i P with (n₁ ≟-Str n₂)
            ... | no ¬p = 𝟘-rec (P refl)
            ... | yes refl-StrId with (ks₁ ≟-Str ks₂)
            ... | no ¬p = 𝟘-rec (P refl)
            ... | yes refl-StrId with (s₁ ≟-Str s₂)
            ... | no ¬p = 𝟘-rec (P refl)
            ... | yes refl-StrId = {!!}

-- with (ks₁ ≟-Str ks₂)
--         ... | no ¬p = refl
--         ... | yes refl-StrId with (s₁ ≟-Str s₂)

            proof (edge i x) fail _ = refl
            proof fail t _ = refl
            proof (edge i x) (valid (te s (ts))) P = P0 s x ts i P
            proof (edge i x) (valid (var x₁)) P = 𝟘-rec (P refl)



        -- | For this we take the following:
        IRecAccessible.Dir RecAccessible:TermZ = of 𝑄
        IRecAccessible.ISet:Dir RecAccessible:TermZ = {!!}
        IRecAccessible.ISet:K RecAccessible:TermZ = {!!}
        IRecAccessible.IDiscreteStr:Dir RecAccessible:TermZ = {!!}
        IRecAccessible.IDiscreteStr:K RecAccessible:TermZ = {!!}
        ⟨ ⟨ IRecAccessible.decompose RecAccessible:TermZ ⟩ ⟩ = decomp
        INatural.naturality (of IRecAccessible.decompose RecAccessible:TermZ) f t i e = naturality-decomp ⟨ f ⟩ t e i
        IRecAccessible.commutes:decompose RecAccessible:TermZ t i e = lem-20.proof t e i
        IRecAccessible.δ-comm RecAccessible:TermZ f {j} {k} e x = lem-25.proof ⟨ f ⟩ e x
        ⟨ ⟨ IRecAccessible.pts RecAccessible:TermZ ⟩ ⟩ _ = fail
        INatural.naturality (of IRecAccessible.pts RecAccessible:TermZ) _ _ = refl
        IRecAccessible.a0 RecAccessible:TermZ = fail
        IRecAccessible.a0-adsorb RecAccessible:TermZ _ = refl
        IRecAccessible.k-a1 RecAccessible:TermZ = {!!}
        IRecAccessible.a1 RecAccessible:TermZ = {!!}
        IRecAccessible.isDecomposableP RecAccessible:TermZ = {!!}
        IRecAccessible.isPureP RecAccessible:TermZ = {!!}
        IRecAccessible.decideDecompose RecAccessible:TermZ = {!!}
        IRecAccessible.makeDec RecAccessible:TermZ = {!!}
        IRecAccessible.makePure RecAccessible:TermZ = {!!}
        IRecAccessible.isWellfounded::≺ RecAccessible:TermZ = {!!}
        IRecAccessible.cancel-δ RecAccessible:TermZ = {!!}

{-
        decomp : {k : K} -> Term σ V k -> V k +-𝒰 (∀(j : K) -> SigEdge j k -> Maybe (Term σ V j))
        decomp {k = k} (te {n = n₁} {ks = ks₁} s₁ ts) = right f
          where
            f : (j : K) → SigEdge j k → Maybe (Term σ V j)
            f .(lookup i _) (edge {n = n₂} {ks = ks₂} i s₂) with (n₁ ≟-Str n₂)
            ... | no ¬p = nothing
            ... | yes refl-StrId with (ks₁ ≟-Str ks₂)
            ... | no ¬p = nothing
            ... | yes refl-StrId with (s₁ ≟-Str s₂)
            ... | no ¬p = nothing
            ... | yes refl-StrId = right (lookup-Term i ts)
        decomp (var x) = left x

        isMono:decomp : ∀ {k} -> (t s : Term σ V k) -> decomp t ≡-Str decomp s -> t ≡-Str s
        isMono:decomp (te x x₁) (te x₂ x₃) p = {!!}
        isMono:decomp (var x) (var .x) refl-StrId = refl-StrId

      -- decomp nothing none = right (λ j ())
      -- decomp {V = V} (just k) (some (te t ts)) = right (f ts)
      --   where f : Terms σ (V) ks -> (j : K) -> SigEdge j (just k) -> Maybe (Term σ _ j)
      --         f = ?
              -- f xs .(just (lookup i _)) (e-arg i x) = {!!}
              -- f xs .nothing (e-noarg x) = {!!}
              -- f .(just (lookup i _)) (e-arg i x) = {!!}
              -- f .nothing (e-noarg x) = {!!}
      -- decomp (just k) (some (var v)) = left v

      RecAccessible:Term : IRecAccessible (Monad:Term σ)
      IRecAccessible.Dir RecAccessible:Term = of 𝑄
      IRecAccessible.ISet:Dir RecAccessible:Term = {!!}
      ⟨ ⟨ IRecAccessible.decompose RecAccessible:Term ⟩ ⟩ _ = decomp
      of IRecAccessible.decompose RecAccessible:Term = {!!}
      IRecAccessible.IMono:decompose RecAccessible:Term = {!!}
      IRecAccessible.wellfounded RecAccessible:Term = {!!}


-}

