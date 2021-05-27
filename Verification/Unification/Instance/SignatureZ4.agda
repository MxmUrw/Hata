
module Verification.Unification.Instance.SignatureZ4 where

open import Verification.Conventions hiding (k)
open import Verification.Core.Category
open import Verification.Core.Order
open import Verification.Core.Type
open import Verification.Core.Homotopy.Level
open import Verification.Core.Category.Monad
open import Verification.Core.Category.Instance.Kleisli
open import Verification.Core.Category.Instance.IdxSet
open import Verification.Core.Category.Limit.Specific
open import Verification.Core.Category.Limit.Kan
open import Verification.Unification.RecAccessible

open import Verification.Core.Syntax.SignatureZ4


instance
  IDiscreteStr:Vec : ∀{A : 𝒰 𝑖} {{_ : IDiscreteStr A}} -> IDiscreteStr (Vec A n)
  (IDiscreteStr:Vec IDiscreteStr.≟-Str a) b = {!!}

  IDiscreteStr:ℕ : IDiscreteStr ℕ
  IDiscreteStr:ℕ = {!!}

  ISet:ℕ : ISet ℕ
  ISet:ℕ = {!!}

  ISet:Vec : ∀{A : 𝒰 𝑖} {{_ : ISet A}} -> ISet (Vec A n)
  ISet:Vec = {!!}

  ISet:Fin-R : ∀{n} -> ISet (Fin-R n)
  ISet:Fin-R = {!!}

module _ {K : 𝒰₀} {{_ : IDiscreteStr K}} {{_ : ISet K}} where

  module _ (σ : Signature) (isInhabited:σ : isInhabited-Sig σ) where
    private
      variable k : K
               ks : Vec K n
               -- j : K

    module _ {{_ : ∀{n k} {ks : Vec K (suc n)} -> IDiscreteStr (σ k ks)}} where


      data isDecomposableP-Term {k : K} {X : K -> 𝒰₀} : Term σ X k -> 𝒰₀ where
        isTe : ∀{ks : Vec K (suc n)} -> (s : σ k ks) -> {ts : Terms σ X ks} -> (tsP : Termsᵥ ts) -> isDecomposableP-Term (te s ts tsP)
        isFail : isDecomposableP-Term fail

      data isPureP-Term {k : K} {X : K -> 𝒰₀} : Term σ X k -> 𝒰₀ where
        isVar : ∀(x : X k) -> isPureP-Term (var x)

      decideDecompose-Term : ∀{k} {X : K -> 𝒰₀} -> ∀ (x : Term σ X k) -> isPureP-Term x +-𝒰 isDecomposableP-Term x
      decideDecompose-Term (te x x₁ tsP) = right (isTe _ _)
      decideDecompose-Term (var x) = left (isVar _)
      decideDecompose-Term fail = right (isFail)


      data SigEdge : (a b : K) -> 𝒰₀ where
        edge : ∀ {k} {ks : Vec K (suc n)} -> (i : Fin-R (suc n)) -> σ k ks -> SigEdge (lookup i ks) k
        fail : ∀{a : K} -> SigEdge a a

      get-a1-k : K -> K
      get-a1-k k =
        let _ , ks , _ = isInhabited:σ k
        in lookup zero ks

      get-a1 : (k : K) -> SigEdge (get-a1-k k) k
      get-a1 k =
        let _ , ks , x = isInhabited:σ k
        in edge zero x

      decide-e0-Term : ∀{k} {X : K -> 𝒰₀} -> (x : Term σ X k) -> Decision (x ≡-Str fail)
      decide-e0-Term (te s ts tsP) = no (λ ())
      decide-e0-Term (var x) = no (λ ())
      decide-e0-Term fail = yes refl

      𝑄 : Quiver ⊥
      ⟨ 𝑄 ⟩ = K
      IQuiver.Edge (of 𝑄) = SigEdge
      IQuiver._≈_ (of 𝑄) = _≡_
      IQuiver.IEquivInst (of 𝑄) = IEquiv:Path

      -- compare-sig : ∀{k j₁ j₂ : K} -> {n₁ n₂ : ℕ} -> (s )

      -- pattern failv = var (left (↥ tt))

      module _ {V : K -> 𝒰₀} where
        lookup-Term : ∀{ks : Vec K (n)} -> (i : Fin-R (n)) -> Terms σ V ks -> Term σ V (lookup i ks)
        lookup-Term zero    (t ∷ ts) = t
        lookup-Term (suc i) (t ∷ ts) = lookup-Term i ts

        module lem-05 where
          proof : ∀{ks : Vec K (n)} -> (i : Fin-R (n)) -> (ts : Terms σ V ks) -> lookup-Term i ts ⊏-Terms ts
          proof zero (t ∷ ts) = this
          proof (suc i) (t ∷ ts) = t ∷ proof i ts

      module _ {V : K -> 𝒰₀} where
        lookup-Term-try : ∀{n₁ n₂ : ℕ} {ks₁ : Vec K (suc n₁)} {ks₂ : Vec K (suc n₂)} (s₁ : σ k ks₁) (s₂ : σ k ks₂) (i : Fin-R (suc n₂)) (ts : Terms σ V ks₁) -> (Term σ V (lookup i ks₂))
        lookup-Term-try {n₁ = n₁} {n₂} {ks₁} {ks₂} s₁ s₂ i ts with (n₁ ≟-Str n₂)
        ... | no ¬p = fail
        ... | yes refl-StrId with (ks₁ ≟-Str ks₂)
        ... | no ¬p = fail
        ... | yes refl-StrId with (s₁ ≟-Str s₂)
        ... | no ¬p = fail
        ... | yes refl-StrId = ((lookup-Term i ts))

        lookup-Term-try-⊏ : ∀{n₁ n₂ : ℕ} {ks₁ : Vec K (suc n₁)} {ks₂ : Vec K (suc n₂)} (s₁ : σ k ks₁) (s₂ : σ k ks₂) (i : Fin-R (suc n₂)) (ts : Terms σ V ks₁) (tsP : Termsᵥ ts)
                          -> lookup-Term-try s₁ s₂ i (ts) ⊏ te s₁ ts tsP

        lookup-Term-try-⊏ {n₁ = n₁} {n₂} {ks₁} {ks₂} s₁ s₂ i ts tsP with (n₁ ≟-Str n₂)
        ... | no ¬p = fail (λ ())
        ... | yes refl-StrId with (ks₁ ≟-Str ks₂)
        ... | no ¬p = fail (λ ())
        ... | yes refl-StrId with (s₁ ≟-Str s₂)
        ... | no ¬p = fail (λ ())
        ... | yes refl-StrId = te (lem-05.proof i ts)


        eval-lookup-Term : ∀ {n₁ n₂} -> ∀{k} -> ∀ {ks₁ : Vec K (suc n₁)} {ks₂ : Vec K (suc n₂)} ->
             (s₁ : σ k ks₁) ->
             (s₂ : σ k ks₂) ->
             (ts  : Terms σ V ks₁) →
             (j₁ : Fin-R (suc n₁))
             (j₂  : Fin-R (suc n₂))
             (pn : n₁ ≡ n₂) ->
             (pks : PathP (λ i -> Vec K (suc (pn i))) ks₁ ks₂)
             (ps : PathP (λ i -> σ k (pks i)) s₁ s₂)
              -> (pj : PathP (λ i -> Fin-R (suc (pn i))) j₁ j₂)
              -> PathP (λ i -> Term σ V (lookup (pj (~ i)) (pks (~ i)))) (lookup-Term-try s₁ s₂ j₂ ts) (lookup-Term j₁ ts)
        eval-lookup-Term {n₁} {n₂} {k} {ks₁} {ks₂} s₁ s₂ ts j₁ j₂ pn pks ps pj with (n₁ ≟-Str n₂)
        ... | no ¬p = 𝟘-rec (¬p (≡→≡-Str pn))
        ... | yes refl-StrId with (ks₁ ≟-Str ks₂) | ≡→≡-Str (hlevel {{ISet:ℕ}} _ _ pn refl)
        ... | no ¬p | refl-StrId = 𝟘-rec (¬p (≡→≡-Str pks))
        ... | yes refl-StrId | refl-StrId with (s₁ ≟-Str s₂) | ≡→≡-Str (hlevel {{ISet:Vec}} _ _ pks refl)
        ... | no ¬p | refl-StrId = 𝟘-rec (¬p (≡→≡-Str ps))
        ... | yes refl-StrId | refl-StrId with ≡→≡-Str pj
        ... | refl-StrId with ≡→≡-Str (hlevel {{ISet:Fin-R}} _ _ pj refl)
        ... | refl-StrId = refl


      module _ {X Y : K -> 𝒰₀} where
        naturality-lookup-Term : (f : ∀{k} -> X k -> Y k) -> ∀{ks : Vec K (n)} -> (i : Fin-R (n)) -> (ts : Terms σ X ks) -> (map-Term f (lookup-Term i ts)) ≡ (lookup-Term i (map-Terms f ts))
        naturality-lookup-Term f zero (t ∷ ts) = refl
        naturality-lookup-Term f (suc i) (t ∷ ts) = naturality-lookup-Term f i ts

      module _ {V : K -> 𝒰₀} where
        commutes:lookup|join : ∀{ks : Vec K (n)} -> (i : Fin-R (n)) -> (ts : Terms σ (Term σ V) ks) -> (join-Term (lookup-Term i ts)) ≡ (lookup-Term i (join-Terms ts))
        commutes:lookup|join zero (t ∷ ts) = refl
        commutes:lookup|join (suc i) (t ∷ ts) = commutes:lookup|join i ts


      module _ {X Y : IdxSet K ⊥} where
        naturality-lookup-Term-try : (f : X ⟶ Y) {k : K} -> ∀ {n n₁}
                                     -> ∀ {ks₁ : Vec K (suc n)} {ks₂ : Vec K (suc n₁)} ->
                            -- (t : TermZ σ X k) →
                            (s₁ : σ k ks₁) ->
                            (s₂ : σ k ks₂) ->
                            (ts  : Terms σ (⟨ X ⟩) ks₁) →
                            (i : Fin-R (suc n₁)) ->
                            (map-Term ⟨ f ⟩) (lookup-Term-try s₁ s₂ i ts) ≡
                                  lookup-Term-try s₁ s₂ i ((map-Terms ⟨ f ⟩ ts))
        naturality-lookup-Term-try f {k} {n} {n₁} {ks₁} {ks₂} s₁ s₂ ts i with (n ≟-Str n₁)
        ... | no ¬p = refl
        ... | yes refl-StrId with (ks₁ ≟-Str ks₂)
        ... | no ¬p = refl
        ... | yes refl-StrId with (s₁ ≟-Str s₂)
        ... | no ¬p = refl
        ... | yes refl-StrId = naturality-lookup-Term ⟨ f ⟩ i ts
        -- naturality-lookup-Term ⟨ f ⟩ i (forget-Terms ts) ∙ cong (lookup-Term i) (commutes:map∣forget-Terms ⟨ f ⟩ ts)


{-
      -- [Theorem]
      -- | The |Monad:TermZ| is recursively accessible.

-}


      -- | First we build the decomposition function:
      decomp : {k : K} {V : K -> 𝒰₀} -> Term σ V k -> (∀{j : K} -> SigEdge j k -> Maybe (Term σ V j))
      decomp t fail = right fail
      -- decomp (te s₁ ts tsP) (edge i s₂) = just (lookup-Term-try s₁ s₂ i (forget-Terms ts))
      decomp (te s₁ ts tsP) (edge i s₂) = just (lookup-Term-try s₁ s₂ i ts)
      decomp (var x₁) (edge i x) = nothing
      decomp fail (edge i x) = right fail
      -- decomp t fail = right (failv)
      -- decomp ((te s₁ ts)) (edge i s₂) = just (lookup-Term-try s₁ s₂ i ts)
      -- decomp (var v) (edge i x) = nothing

      module _ {X Y : IdxSet K ⊥} where
        naturality-decomp : (f : X ⟶ Y) {k : K}
                            (t : Term σ (⟨ X ⟩) k) →
                            ∀{j} -> (e : SigEdge j k) ->
                            map-Maybe (map-Term ⟨ f ⟩) (decomp t e) ≡ decomp (map-Term ⟨ f ⟩ t) e
        naturality-decomp f t fail = refl
        naturality-decomp f fail (edge i x) = refl
        naturality-decomp f (var x₁) (edge i x) = refl
        naturality-decomp f (te s₁ ts tsP) (edge i s₂) = cong right (naturality-lookup-Term-try f s₁ s₂ ts i)
        -- cong right (naturality-lookup-Term-try f s₁ s₂ (forget-Terms ts) i)



      module lem-25 {X Y : K -> 𝒰₀} (f : ∀{k} -> X k ⟶ Term σ Y k) where
          proof : ∀{j k} -> ∀(e : Edge {{of 𝑄}} k j) -> ∀ t -> (decomp t e ≢ nothing) -> map-Maybe (λ a → join-Term {V = Y} (map-Term f a)) (decomp t e)
                  ≡ decomp (join-Term {V = Y} (map-Term f t)) e

          P3 :             ∀ {n₁} -> ∀ {ks₁ : Vec K (suc n₁)} ->
                            -- (t : TermZ σ X k) →
                            (s₁ : σ k ks₁) ->
                            (ts  : Terms σ X ks₁) →
                            (isFail-Terms (join-Terms (map-Terms f ts))) ->
                            -- (isFail-Terms (join-Termsᵥ (map-Termsᵥ f ts))) ->
                            (i : Fin-R (suc n₁)) ->
                            isFail-Term (join-Term (map-Term f (lookup-Term i ts)))
          P3 s ts F i =
            let t = lookup-Term i ts
                Q0 : t ⊏-Terms ts
                Q0 = lem-05.proof i ts

                Q1 : map-Term f t ⊏-Terms map-Terms f ts
                Q1 = map⊏-Terms f Q0

                Q2 : join-Term (map-Term f t) ⊏-Terms join-Terms (map-Terms f ts)
                Q2 = join⊏-Terms Q1

            in fail⊏-Terms Q2 F


          P2 :             ∀ {n₁ n₂} -> ∀ {ks₁ : Vec K (suc n₁)} {ks₂ : Vec K (suc n₂)} ->
                            (s₁ : σ k ks₁) ->
                            (s₂ : σ k ks₂) ->
                            (ts  : Terms σ X ks₁) →
                            (i : Fin-R (suc n₂)) ->
                            (isFail-Terms (join-Terms (map-Terms f ts))) ->
                            (join-Term (map-Term f (lookup-Term-try s₁ s₂ i ts))) ≡ fail
          P2 {k} {n₁} {n₂} {ks₁} {ks₂} s₁ s₂ ts i F with (n₁ ≟-Str n₂)
          ... | no ¬p = refl
          ... | yes refl-StrId with (ks₁ ≟-Str ks₂)
          ... | no ¬p = refl
          ... | yes refl-StrId with (s₁ ≟-Str s₂)
          ... | no ¬p = refl
          ... | yes refl-StrId = cast::isFail-Term (P3 s₁ ts F i)

          P4 :             ∀ {n₁ n₂} -> ∀ {ks₁ : Vec K (suc n₁)} {ks₂ : Vec K (suc n₂)} ->
                            -- (t : TermZ σ X k) →
                            (s₁ : σ k ks₁) ->
                            (s₂ : σ k ks₂) ->
                            (ts  : Terms σ X ks₁) →
                            (i : Fin-R (suc n₂)) ->
                            -- (isFail-Terms (join-Termsᵥ (map-Termsᵥ f ts))) ->
                            (join-Term (map-Term f (lookup-Term-try s₁ s₂ i ts))) ≡ lookup-Term-try s₁ s₂ i (join-Terms (map-Terms f ts))
          P4 {k} {n₁} {n₂} {ks₁} {ks₂} s₁ s₂ ts i with (n₁ ≟-Str n₂)
          ... | no ¬p = refl
          ... | yes refl-StrId with (ks₁ ≟-Str ks₂)
          ... | no ¬p = refl
          ... | yes refl-StrId with (s₁ ≟-Str s₂)
          ... | no ¬p = refl
          ... | yes refl-StrId =
            let Q0 = join-Term (map-Term f (lookup-Term i ts)) ≡⟨ cong join-Term (naturality-lookup-Term f i ts) ⟩
                    join-Term (lookup-Term i (map-Terms f ts)) ≡⟨ commutes:lookup|join i _ ⟩
                    lookup-Term i (join-Terms (map-Terms f ts)) ∎
            in Q0



          proof fail t P = refl
          proof (edge i x) fail P = refl
          proof (edge i x) (var x₁) P = 𝟘-rec (P refl)
          proof (edge i s₂) (te s₁ ts tsP) P with split-+-Str (reduce-Terms (join-Terms (map-Terms f ts)))
          ... | left (aF , P') = cong right (P2 s₁ s₂ ts i aF)
          ... | just ((ts') , P') = cong right (P4 s₁ s₂ ts i)



      module lem-30 {k} {X : K -> 𝒰₀} {x : Term σ X k} where
        proof : isDecomposableP-Term x → {j : K} (e : SigEdge j k) → ∑ (λ y → decomp x e ≡-Str just y)
        proof (isTe s ts) (edge i x) = _ , refl
        proof (isTe s ts) fail = _ , refl
        proof isFail (edge i x) = _ , refl
        proof isFail fail = _ , refl

      module lem-40 {k} {X : K -> 𝒰₀} {x : Term σ X k} where
        proof : isPureP-Term x →
              (decomp x (get-a1 k) ≡-Str nothing) ×-𝒰
              ((∑ (λ x' → x ≡-Str var x')))
        proof (isVar x) = refl , (_ , refl)


      module lem-60 {k} {X : K -> 𝒰₀} where
        proof : (x y : Term σ X k) →
              isDecomposableP-Term x →
              isDecomposableP-Term y →
              ({j : K} (e : SigEdge j k) → decomp x e ≡ decomp y e) → x ≡ y

        P0 : ∀{k} -> {t s : Term σ X k} -> isFail-Term t -> ¬ isFail-Term s -> t ≡ s -> 𝟘-𝒰
        P0 fail sF p with ≡→≡-Str p
        ... | refl-StrId = sF fail

        P1 :  ∀ {n₁ n₂} -> ∀ {ks₁ : Vec K (suc n₁)} {ks₂ : Vec K (suc n₂)} ->
             (s₁ : σ k ks₁) ->
             (s₂ : σ k ks₂) ->
             (ts  : Terms σ X ks₁) →
             (n₁ ≢-Str n₂) ->
             (i : Fin-R (suc n₂)) -> isFail-Term (lookup-Term-try s₁ s₂ i ts)
        P1 {n₁} {n₂} {ks₁} {ks₂} s₁ s₂ ts pn i with (n₁ ≟-Str n₂)
        ... | yes refl-StrId = 𝟘-rec (pn refl)
        ... | no ¬p = fail

        P2 :  ∀ {n₁ n₂} -> ∀ {ks₁ : Vec K (suc n₁)} {ks₂ : Vec K (suc n₂)} ->
             (s₁ : σ k ks₁) ->
             (s₂ : σ k ks₂) ->
             (ts  : Terms σ X ks₁) →
             (pn : n₁ ≡ n₂) ->
             (pks : PathP (λ i -> Vec K (suc (pn i))) ks₁ ks₂ -> 𝟘-𝒰)
             (i : Fin-R (suc n₂)) -> isFail-Term (lookup-Term-try s₁ s₂ i ts)
        P2 {n₁} {n₂} {ks₁} {ks₂} s₁ s₂ ts pn pks i with (n₁ ≟-Str n₂)
        ... | no ¬p = fail
        ... | yes refl-StrId with (ks₁ ≟-Str ks₂) | ≡→≡-Str (hlevel {{ISet:ℕ}} _ _ pn refl)
        ... | no ¬p | refl-StrId = fail
        ... | yes refl-StrId | refl-StrId = 𝟘-rec (pks refl)

        P3 :  ∀ {n₁ n₂} -> ∀ {ks₁ : Vec K (suc n₁)} {ks₂ : Vec K (suc n₂)} ->
             (s₁ : σ k ks₁) ->
             (s₂ : σ k ks₂) ->
             (ts  : Terms σ X ks₁) →
             (pn : n₁ ≡ n₂) ->
             (pks : PathP (λ i -> Vec K (suc (pn i))) ks₁ ks₂)
             (ps : PathP (λ i -> σ k (pks i)) s₁ s₂ -> 𝟘-𝒰)
             (i : Fin-R (suc n₂)) -> isFail-Term (lookup-Term-try s₁ s₂ i ts)
        P3 {n₁} {n₂} {ks₁} {ks₂} s₁ s₂ ts pn pks ps i with (n₁ ≟-Str n₂)
        ... | no ¬p = fail
        ... | yes refl-StrId with (ks₁ ≟-Str ks₂) | ≡→≡-Str (hlevel {{ISet:ℕ}} _ _ pn refl)
        ... | no ¬p | refl-StrId = fail
        ... | yes refl-StrId | refl-StrId with (s₁ ≟-Str s₂) | ≡→≡-Str (hlevel {{ISet:Vec}} _ _ pks refl)
        ... | no ¬p | refl-StrId = fail -- 𝟘-rec (¬p (≡→≡-Str ps))
        ... | yes refl-StrId | refl-StrId = 𝟘-rec (ps refl) -- nofailEdge ts


        P4 : ∀{ks : Vec K (n)} -> (ts₁ ts₂ : Terms σ X ks) -> (∀ i -> lookup-Term i ts₁ ≡ lookup-Term i ts₂) -> ts₁ ≡ ts₂
        P4 [] [] _ = refl
        P4 (t ∷ ts) (s ∷ ss) P i = P zero i ∷ P4 ts ss (λ j -> P (suc j)) i


        -- P1 :   ∀ {n₁} -> ∀ {ks₁ : Vec K (suc n₁)}
        --      (s₁ : σ k ks₁) ->
        --      -- (s₂ : σ k ks₂) ->
        --      (ts  : TermsZ2 σ X ks₁) →
        --      (i : Fin-R (suc n₁)) -> lookup-Term-try s₁ s₁ i ts ≡ lookup-Term i ts
        -- P1 = {!!}

        -- failv≢var : ∀{x : X k} -> Path (TermZ2 σ X k) failv (var (right x)) -> 𝟘-𝒰
        -- failv≢var p with ≡→≡-Str p
        -- ... | ()

        nofailEdge : ∀{ks : Vec K n} -> {ts : Terms σ X ks} -> (tsP : Termsᵥ ts) -> ∑ λ j -> ¬ isFail-Term (lookup-Term j (ts))
        nofailEdge (te s ts₁ tsP ∷ ts) = zero , λ {()}
        nofailEdge (var x ∷ ts) = zero , λ {()}
        nofailEdge (fail∷ tsP) = let j , jF = nofailEdge tsP in suc j , jF
        -- nofailEdge (te s ts₁ ∷ ts) = zero , λ {()}
        -- nofailEdge (var x ∷ ts) = zero , λ {()}
        -- nofailEdge (fail∷ ts) = let j , jF = nofailEdge ts in suc j , jF


        nofailEdge2 :  ∀ {n₁ n₂} -> ∀ {ks₁ : Vec K (suc n₁)} {ks₂ : Vec K (suc n₂)} ->
             (s₁ : σ k ks₁) ->
             (s₂ : σ k ks₂) ->
             {ts  : Terms σ X ks₁} →
             (tsP : Termsᵥ ts)
             (pn : n₁ ≡ n₂) ->
             (pks : PathP (λ i -> Vec K (suc (pn i))) ks₁ ks₂)
             (ps : PathP (λ i -> σ k (pks i)) s₁ s₂)
              -> ∑ λ j -> ¬ isFail-Term (lookup-Term-try s₁ s₂ j ts)
        nofailEdge2 {n₁} {n₂} {ks₁} {ks₂} s₁ s₂ ts pn pks ps with (n₁ ≟-Str n₂)
        ... | no ¬p = 𝟘-rec (¬p (≡→≡-Str pn))
        ... | yes refl-StrId with (ks₁ ≟-Str ks₂) | ≡→≡-Str (hlevel {{ISet:ℕ}} _ _ pn refl)
        ... | no ¬p | refl-StrId = 𝟘-rec (¬p (≡→≡-Str pks))
        ... | yes refl-StrId | refl-StrId with (s₁ ≟-Str s₂) | ≡→≡-Str (hlevel {{ISet:Vec}} _ _ pks refl)
        ... | no ¬p | refl-StrId = 𝟘-rec (¬p (≡→≡-Str ps))
        ... | yes refl-StrId | refl-StrId = nofailEdge ts

        compare : (x y : Term σ X k) ->
              isDecomposableP-Term x →
              isDecomposableP-Term y →
              ({j : K} (e : SigEdge j k) → decomp x e ≡ decomp y e) ->
              (∑ λ j -> ∑ λ (e : SigEdge j k) -> decomp x e ≡ decomp y e -> 𝟘-𝒰) +-𝒰 (x ≡ y)
        compare (fail) (te {n₂} {ks₂} s₂ ts₂ tsP₂) (isFail) (isTe s₂ tsP₂) Pd =
          let j , Fj = nofailEdge2 s₂ s₂ tsP₂ refl refl refl
          in left (_ , edge j s₂ ,
                  λ p -> let Q1 = isInjective:right p
                             Q2 = fail
                         in P0 Q2 Fj Q1
                  )
        compare (te {n₁} {ks₁} s₁ ts₁ tsP₁) (fail) (isTe s₁ tsP₁) (isFail) Pd =
          let j , Fj = nofailEdge2 s₁ s₁ tsP₁ refl refl refl
          in left (_ , edge j s₁ ,
                  λ p -> let Q1 = isInjective:right p
                             Q2 = fail
                         in P0 Q2 Fj (sym Q1)
                  )
        compare fail fail isFail isFail Pd = right refl
        compare (te {n₁} {ks₁} s₁ ts₁ tsP₁) (te {n₂} {ks₂} s₂ ts₂ tsP₂) (isTe s₁ tsP₁) (isTe s₂ tsP₂) Pd with n₁ ≟-Str n₂
        ... | no ¬p =
          let j , Fj = nofailEdge2 s₂ s₂ tsP₂ refl refl refl
          in left (_ , edge j s₂ ,
                  λ p -> let Q1 = isInjective:right p
                             Q2 = P1 s₁ s₂ (ts₁) ¬p j
                         in P0 Q2 Fj Q1
                  )
        ... | yes refl-StrId with (ks₁ ≟-Str ks₂)
        ... | no ¬p =
          let j , Fj = nofailEdge2 s₂ s₂ tsP₂ refl refl refl
          in left (_ , edge j s₂ ,
                  λ p -> let Q1 = isInjective:right p
                             Q2 = P2 s₁ s₂ (ts₁) refl (λ {p -> ¬p (≡→≡-Str p)}) j
                         in P0 Q2 Fj Q1
                  )
        ... | yes refl-StrId with (s₁ ≟-Str s₂)
        ... | no ¬p =
          let j , Fj = nofailEdge2 s₂ s₂ tsP₂ refl refl refl
          in left (_ , edge j s₂ ,
                  λ p -> let Q1 = isInjective:right p
                             Q2 = P3 s₁ s₂ ts₁ refl refl (λ {p -> ¬p (≡→≡-Str p)}) j
                         in P0 Q2 Fj Q1
                  )
        ... | yes refl-StrId =
             let Q0 : (j : Fin-R (suc n₁)) → lookup-Term j ts₁ ≡ lookup-Term j ts₂
                 Q0 j = eval-lookup-Term s₁ s₁ (ts₁) j j refl refl refl refl ⁻¹
                        ∙ isInjective:right (Pd (edge j s₁))
                        ∙ eval-lookup-Term s₂ s₂ (ts₂) j j refl refl refl refl
                 Q1 : ts₁ ≡ ts₂
                 Q1 = P4 ts₁ ts₂ Q0
                 Q2 : Path (∑ Termsᵥ) (ts₁ , tsP₁) (_ , tsP₂)
                 Q2 = byFirstP Q1
              -- Q2 = ≡-Str→≡ (isInjective:forget-Terms (≡→≡-Str Q1))
        --   in right (λ i -> te s₁ (Q2 i))
            in right (λ i -> te s₁ (Q2 i .fst) (Q2 i .snd))

        proof x y Px Py Pd with compare x y Px Py Pd
        ... | left (j , e , ¬Pd) = 𝟘-rec (¬Pd (Pd e))
        ... | just p = p

      module lem-70 {X : K -> 𝒰₀} where
        proof : ∀{k j} -> (x : Term σ X k) -> (y : Term σ X j)
                    → (y ≢-Str fail) ×-𝒰 (∑ (λ e → decomp y e ≡-Str just x))
              -> x ⊏ y
        proof .(lookup-Term-try s x₁ i (ts)) (te s ts tsP) (P , edge i x₁ , refl-StrId) = lookup-Term-try-⊏ s x₁ i ts tsP
        proof .fail (te s ts tsP) (P , fail , refl-StrId) = fail P
        proof .fail (var x₁) (P , fail , refl-StrId) = fail P
        proof x fail (P , Q) = 𝟘-rec (P refl)


      -- | For this we take the following:
      RecAccessible:TermZ : IRecAccessible (Monad:Term σ)
      IRecAccessible.Dir RecAccessible:TermZ = of 𝑄
      IRecAccessible.ISet:Dir RecAccessible:TermZ = {!!}
      IRecAccessible.ISet:K RecAccessible:TermZ = {!!}
      IRecAccessible.IDiscreteStr:Dir RecAccessible:TermZ = {!!}
      IRecAccessible.IDiscreteStr:K RecAccessible:TermZ = {!!}
      ⟨ ⟨ IRecAccessible.decompose RecAccessible:TermZ ⟩ ⟩ = decomp
      INatural.naturality (of IRecAccessible.decompose RecAccessible:TermZ) f t i e = naturality-decomp f t e i
      -- IRecAccessible.commutes:decompose RecAccessible:TermZ t = {!!} -- lem-20.proof t e i
      IRecAccessible.δ-comm RecAccessible:TermZ f {j} {k} e x = lem-25.proof ⟨ f ⟩ e x
      -- ⟨ ⟨ IRecAccessible.pts RecAccessible:TermZ ⟩ ⟩ _ = fail -- failv
      -- INatural.naturality (of IRecAccessible.pts RecAccessible:TermZ) _ _ = refl
      IRecAccessible.e0 RecAccessible:TermZ = fail
      IRecAccessible.a0 RecAccessible:TermZ = fail
      IRecAccessible.a0-adsorb RecAccessible:TermZ _ = refl
      IRecAccessible.k-a1 RecAccessible:TermZ = get-a1-k
      IRecAccessible.a1 RecAccessible:TermZ = get-a1 _
      IRecAccessible.isDecomposableP RecAccessible:TermZ = isDecomposableP-Term
      IRecAccessible.isPureP RecAccessible:TermZ = isPureP-Term
      IRecAccessible.decideDecompose RecAccessible:TermZ = decideDecompose-Term
      IRecAccessible.decide-e0 RecAccessible:TermZ x = decide-e0-Term x
      IRecAccessible.makeDec RecAccessible:TermZ = lem-30.proof
      IRecAccessible.makePure RecAccessible:TermZ = lem-40.proof
      IRecAccessible._≺P_ RecAccessible:TermZ (x) (y) = x .snd ⊏ y .snd
      IRecAccessible.recreate-≺ RecAccessible:TermZ = lem-70.proof _ _
      IRecAccessible.isWellfounded::≺P RecAccessible:TermZ = isWellfounded::⊏
      IRecAccessible.cancel-δ RecAccessible:TermZ = lem-60.proof


