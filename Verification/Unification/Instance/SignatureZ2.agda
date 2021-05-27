
module Verification.Unification.Instance.SignatureZ2 where

open import Verification.Conventions hiding (k)
open import Verification.Core.Category
open import Verification.Core.Order
open import Verification.Core.Type
open import Verification.Core.Category.Monad
open import Verification.Core.Category.Instance.Kleisli
open import Verification.Core.Category.Instance.IdxSet
open import Verification.Core.Category.Limit.Specific
open import Verification.Core.Category.Limit.Kan
open import Verification.Unification.RecAccessible

open import Verification.Core.Syntax.SignatureZ2

instance
  IDiscreteStr:Vec : ∀{A : 𝒰 𝑖} {{_ : IDiscreteStr A}} -> IDiscreteStr (Vec A n)
  (IDiscreteStr:Vec IDiscreteStr.≟-Str a) b = {!!}

  IDiscreteStr:ℕ : IDiscreteStr ℕ
  IDiscreteStr:ℕ = {!!}

_≢-Str_ : ∀{A : 𝒰 𝑖} -> (a b : A) -> 𝒰 𝑖
_≢-Str_ a b = ¬ a ≡-Str b

module _ {K : 𝒰₀} {{_ : IDiscreteStr K}} where

  module _ (σ : Signature) (isInhabited:σ : isInhabited-Sig σ) where
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
      data isDecomposableP-Term {k : K} {X : K -> 𝒰₀} : TermZ2 σ X k -> 𝒰₀ where
        isTe : ∀{ks : Vec K (suc n)} -> (s : σ k ks) -> (ts : TermsZ2 σ X ks) -> isDecomposableP-Term (te s ts)

      data isPureP-Term {k : K} {X : K -> 𝒰₀} : TermZ2 σ X k -> 𝒰₀ where
        isVar : ∀(x : ⇈ X k) -> isPureP-Term (var x)

      decideDecompose-Term : ∀{k} {X : K -> 𝒰₀} -> ∀ (x : TermZ2 σ X k) -> isPureP-Term x +-𝒰 isDecomposableP-Term x
      decideDecompose-Term (te x x₁) = right (isTe _ _)
      decideDecompose-Term (var x) = left (isVar _)

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

      𝑄 : Quiver ⊥
      ⟨ 𝑄 ⟩ = K
      IQuiver.Edge (of 𝑄) = SigEdge
      IQuiver._≈_ (of 𝑄) = _≡_
      IQuiver.IEquivInst (of 𝑄) = IEquiv:Path

      -- compare-sig : ∀{k j₁ j₂ : K} -> {n₁ n₂ : ℕ} -> (s )

      pattern failv = var (left (↥ tt))

      module _ {V : K -> 𝒰₀} where
        lookup-Term : ∀{ks : Vec K (n)} -> (i : Fin-R (n)) -> Terms σ V ks -> Term σ V (lookup i ks)
        lookup-Term zero    (t ∷ ts) = t
        lookup-Term (suc i) (t ∷ ts) = lookup-Term i ts

      module _ {V : K -> 𝒰₀} where
        lookup-Term-try : ∀{n₁ n₂ : ℕ} {ks₁ : Vec K (suc n₁)} {ks₂ : Vec K (suc n₂)} (s₁ : σ k ks₁) (s₂ : σ k ks₂) (i : Fin-R (suc n₂)) (ts : TermsZ2 σ V ks₁) -> (TermZ2 σ V (lookup i ks₂))
        lookup-Term-try {n₁ = n₁} {n₂} {ks₁} {ks₂} s₁ s₂ i ts with (n₁ ≟-Str n₂)
        ... | no ¬p = failv
        ... | yes refl-StrId with (ks₁ ≟-Str ks₂)
        ... | no ¬p = failv
        ... | yes refl-StrId with (s₁ ≟-Str s₂)
        ... | no ¬p = failv
        ... | yes refl-StrId = ((lookup-Term i ts))
        -- ... | no ¬p = nothing
        -- ... | yes refl-StrId with (ks₁ ≟-Str ks₂)
        -- ... | no ¬p = nothing
        -- ... | yes refl-StrId with (s₁ ≟-Str s₂)
        -- ... | no ¬p = nothing
        -- ... | yes refl-StrId = right ((lookup-Term i ts))


      -- module _ {X Y : K -> 𝒰₀} where
      --   naturality-lookup-Term : (f : ∀{k} -> X k -> Y k) -> ∀{ks : Vec K (n)} -> (i : Fin-R (n)) -> (ts : Terms σ X ks) -> (map-Term f (lookup-Term i ts)) ≡ (lookup-Term i (map-Terms f ts))
      --   naturality-lookup-Term f zero (t ∷ ts) = refl
      --   naturality-lookup-Term f (suc i) (t ∷ ts) = naturality-lookup-Term f i ts

      module _ {X Y : IdxSet K ⊥} where
        naturality-lookup-Term : (f : X ⟶ Y) -> ∀{ks : Vec K (n)} -> (i : Fin-R (n)) -> (ts : TermsZ2 σ ⟨ X ⟩ ks) -> (map-TermZ2 f (lookup-Term i ts)) ≡ (lookup-Term i (map-TermsZ2 f ts))
        naturality-lookup-Term f zero (t ∷ ts) = refl
        naturality-lookup-Term f (suc i) (t ∷ ts) = naturality-lookup-Term f i ts

      module _ {X Y : IdxSet K ⊥} where
        naturality-lookup-Term-try : (f : X ⟶ Y) {k : K} -> ∀ {n n₁}
                                     -> ∀ {ks₁ : Vec K (suc n)} {ks₂ : Vec K (suc n₁)} ->
                            -- (t : TermZ σ X k) →
                            (s₁ : σ k ks₁) ->
                            (s₂ : σ k ks₂) ->
                            (ts  : Terms σ (⇈ ⟨ X ⟩) ks₁) →
                            (i : Fin-R (suc n₁)) ->
                            (map-TermZ2 f) (lookup-Term-try s₁ s₂ i ts) ≡
                                  lookup-Term-try s₁ s₂ i (map-TermsZ2 f ts)
        naturality-lookup-Term-try f {k} {n} {n₁} {ks₁} {ks₂} s₁ s₂ ts i with (n ≟-Str n₁)
        ... | no ¬p = refl
        ... | yes refl-StrId with (ks₁ ≟-Str ks₂)
        ... | no ¬p = refl
        ... | yes refl-StrId with (s₁ ≟-Str s₂)
        ... | no ¬p = refl
        ... | yes refl-StrId = λ j -> ((naturality-lookup-Term f i ts j))

      -- [Theorem]
      -- | The |Monad:TermZ| is recursively accessible.


      -- | First we build the decomposition function:
      decomp : {k : K} {V : K -> 𝒰₀} -> Term σ (⇈ V) k -> (∀{j : K} -> SigEdge j k -> Maybe (Term σ (⇈ V) j))
      decomp t fail = right (failv)
      decomp ((te s₁ ts)) (edge i s₂) = just (lookup-Term-try s₁ s₂ i ts)
      decomp (var v) (edge i x) = nothing
      -- decomp _ fail = right fail
      -- decomp fail (edge _ _) = right fail
      -- decomp (valid (var x)) (edge _ _) = nothing
      -- decomp (valid (te s₁ ts)) (edge i s₂) = lookup-Term-try s₁ s₂ i ts

      module _ {X Y : IdxSet K ⊥} where
        naturality-decomp : (f : X ⟶ Y) {k : K}
                            (t : TermZ2 σ (⟨ X ⟩) k) →
                            ∀{j} -> (e : SigEdge j k) ->
                            map-Maybe (map-TermZ2 f) (decomp t e) ≡ decomp (map-TermZ2 f t) e
        naturality-decomp f t fail = refl
        naturality-decomp f (te s₁ ts) (edge i s₂) = cong right (naturality-lookup-Term-try f s₁ s₂ ts i)
        naturality-decomp f (var x₁) (edge i x) = refl

      -- module lem-20 {X : K -> 𝒰₀} where
      --   proof : (t : TermZ σ (TermZ σ X) k) →
      --           ∀{j} -> (e : SigEdge j k) ->
      --           map-Maybe join-TermZ (decomp t e) ≡ decomp (join-TermZ t) e
      --   proof t fail = refl
      --   proof fail (edge i x) = refl
      --   proof (valid (te x₁ x₂)) (edge i x) = {!!}
      --   proof (valid (var fail)) (edge i x) = {!!}
      --   proof (valid (var (valid x₁))) (edge i x) = {!!}

-- Goal: map-Maybe (λ a → join-TermZ2 (map-TermZ2 f a))
--       (lookup-Term-try x₁ x i x₂)
--       ≡
--       lookup-Term-try x₁ x i
--       (join-Terms
--        (map-Terms
--         ⟨
--         isCoproduct.[ hasCoproducts.isCoproduct:+ hasCoproducts:IdxSet ,
--         ` (λ {k} → comp-𝒰 left (λ x₃ → var x₃)) ` ]
--         (idxSetHom id-𝒰)
--         ⟩
--         (map-Terms ⟨ IFunctor.map (of ` _+-IdxSet_ 𝟙 `) f ⟩ x₂)))

      module lem-25 {X Y : IdxSet K ⊥} (f : X ⟶ IdxTermZ2 σ Y) where
        interleaved mutual
          proof : ∀{j k} -> ∀(e : Edge {{of 𝑄}} k j) -> ∀ t -> (decomp t e ≢ nothing) -> map-Maybe (λ a → join-TermZ2 {V = Y} (map-TermZ2 f a)) (decomp t e)
                  ≡ decomp (join-TermZ2 {V = Y} (map-TermZ2 f t)) e

          ζ' : ∀ {k : K} ->
                            -- (t : TermZ σ X k) →
                            (ts  : TermZ2 σ ⟨ X ⟩ k) → _ -- TermsZ2 σ ⟨ X ⟩ ks₁
          ζ' ts = (map-Term
              ⟨
              [,]-IdxSet ⟨ Terminal:IdxSet ⟩
              (IdxTerm σ (⟨ Terminal:IdxSet ⟩ +-IdxSet Y))
              (IdxTerm σ (⟨ Terminal:IdxSet ⟩ +-IdxSet Y))
              (⌘ (λ {k} a → var (left a))) (⌘ (λ a → a))
              ⟩
              (map-Term
                ⟨
                [,]-IdxSet ⟨ Terminal:IdxSet ⟩ X
                (⟨ Terminal:IdxSet ⟩ +-IdxSet
                (⌘_ (Term σ (λ k → Lift 𝟙-𝒰 +-𝒰 ⟨ Y ⟩ k))))
                (⌘ (λ {k} a → left a)) (⌘ (λ {k} a → just (⟨ f ⟩ a)))
                ⟩ ts))
          ζ : ∀ {n} -> ∀ {ks₁ : Vec K (n)} ->
                            -- (t : TermZ σ X k) →
                            (ts  : TermsZ2 σ ⟨ X ⟩ ks₁) → _ -- TermsZ2 σ ⟨ X ⟩ ks₁
          ζ ts = (map-Terms
              ⟨
              [,]-IdxSet ⟨ Terminal:IdxSet ⟩
              (IdxTerm σ (⟨ Terminal:IdxSet ⟩ +-IdxSet Y))
              (IdxTerm σ (⟨ Terminal:IdxSet ⟩ +-IdxSet Y))
              (⌘ (λ {k} a → var (left a))) (⌘ (λ a → a))
              ⟩
              (map-Terms
                ⟨
                [,]-IdxSet ⟨ Terminal:IdxSet ⟩ X
                (⟨ Terminal:IdxSet ⟩ +-IdxSet
                (⌘_ (Term σ (λ k → Lift 𝟙-𝒰 +-𝒰 ⟨ Y ⟩ k))))
                (⌘ (λ {k} a → left a)) (⌘ (λ {k} a → just (⟨ f ⟩ a)))
                ⟩ ts))


          P1 : ∀ {n} -> ∀ {ks₁ : Vec K (n)} ->
                            (ts  : TermsZ2 σ ⟨ X ⟩ ks₁) →
                            (i : Fin-R (n)) ->
                            join-Term (ζ' (lookup-Term i ts)) ≡ lookup-Term i (join-Terms (ζ ts))
          P1 (t ∷ ts) zero = refl
          P1 (t ∷ ts) (suc i) = P1 ts i




          P0 :             ∀ {n n₁} -> ∀ {ks₁ : Vec K (suc n)} {ks₂ : Vec K (suc n₁)} ->
                            -- (t : TermZ σ X k) →
                            (s₁ : σ k ks₁) ->
                            (s₂ : σ k ks₂) ->
                            (ts  : TermsZ2 σ ⟨ X ⟩ ks₁) →
                            (i : Fin-R (suc n₁)) ->
                            -- (decomp t e ≢ nothing) ->
                            -- (lookup-Term-try s₁ s₂ i ts ≢ nothing) ->
                            join-TermZ2 {V = Y} (map-TermZ2 f (lookup-Term-try s₁ s₂ i ts))
                                  ≡
                                  lookup-Term-try s₁ s₂ i
                                  (join-Terms
                                  -- (map-Terms ⟨ [ ⌘ (λ {k} a → var (left a)) , ⌘ (λ a → a) ]-IdxSet ⟩
                                  -- (map-Terms
                                  --   ⟨ [ ⌘ (λ {k} a → left a) , ⌘ (λ {k} a → just (⟨ f ⟩ a)) ]-IdxSet ⟩
                                  --   ts)))

                                  (map-Terms
                                  ⟨
                                  [,]-IdxSet ⟨ Terminal:IdxSet ⟩
                                  (IdxTerm σ (⟨ Terminal:IdxSet ⟩ +-IdxSet Y))
                                  (IdxTerm σ (⟨ Terminal:IdxSet ⟩ +-IdxSet Y))
                                  (⌘ (λ {k} a → var (left a))) (⌘ (λ a → a))
                                  ⟩
                                  (map-Terms
                                    ⟨
                                    [,]-IdxSet ⟨ Terminal:IdxSet ⟩ X
                                    (⟨ Terminal:IdxSet ⟩ +-IdxSet
                                    (⌘_ (Term σ (λ k → Lift 𝟙-𝒰 +-𝒰 ⟨ Y ⟩ k))))
                                    (⌘ (λ {k} a → left a)) (⌘ (λ {k} a → just (⟨ f ⟩ a)))
                                    ⟩
                                    ts)))

          P0 {k} {n₁} {n₂} {ks₁} {ks₂} s₁ s₂ ts i with (n₁ ≟-Str n₂)
          ... | no ¬p = refl
          ... | yes refl-StrId with (ks₁ ≟-Str ks₂)
          ... | no ¬p = refl
          ... | yes refl-StrId with (s₁ ≟-Str s₂)
          ... | no ¬p = refl
          ... | yes refl-StrId = (P1 ts i)

          proof (edge i s₂) (te s₁ ts) P = cong right (P0 s₁ s₂ ts i)
          proof (edge i x) (var x₁) P = 𝟘-rec (P refl)
          proof fail t P = refl

          -- proof (edge i s₂) (te s₁ ts) P = P0 s₁ s₂ ts i P
          -- proof (edge i x) (var x₁) P = 𝟘-rec (P refl)
          -- proof fail t P = refl

                            -- map-Maybe (λ a -> join-TermZ (map-TermZ f a)) (lookup-Term-try s₁ s₂ i ts) ≡
                            --       decomp (join-Term (te s₁ (map-Terms f ts))) (edge i s₂)
                                  -- lookup-Term-try s₁ s₂ i (map-Terms f ts)
          -- P0 {k} {n₁} {n₂} {ks₁} {ks₂} s₁ s₂ ts i P with (n₁ ≟-Str n₂)
          -- ... | no ¬p = 𝟘-rec (P refl)
          -- ... | yes refl-StrId with (ks₁ ≟-Str ks₂)
          -- ... | no ¬p = 𝟘-rec (P refl)
          -- ... | yes refl-StrId with (s₁ ≟-Str s₂)
          -- ... | no ¬p = 𝟘-rec (P refl)
          -- ... | yes refl-StrId = {!!}


          -- proof (edge i x) fail _ = refl
          -- proof fail t _ = refl
          -- proof (edge i x) (valid (te s (ts))) P = P0 s x ts i P
          -- proof (edge i x) (valid (var x₁)) P = 𝟘-rec (P refl)

      module lem-30 {k} {X : K -> 𝒰₀} {x : TermZ2 σ X k} where
        proof : isDecomposableP-Term x → {j : K} (e : SigEdge j k) → ∑ (λ y → decomp x e ≡-Str just y)
        proof (isTe s ts) (edge i x) = _ , refl
        proof (isTe s ts) fail = _ , refl

      module lem-40 {k} {X : K -> 𝒰₀} {x : TermZ2 σ X k} where
        proof : isPureP-Term x →
                (decomp x (get-a1 k) ≡-Str nothing) ×-𝒰
                ((x ≡-Str failv) +-𝒰
                (∑ (λ x' → x ≡-Str (var (right x' )))))
        proof (isVar (left (↥ tt))) = refl , (left refl)
        proof (isVar (just x)) = refl , right (_ , refl)

      module lem-60 {k} {X : K -> 𝒰₀} where
        proof : (x y : TermZ2 σ X k) →
              isDecomposableP-Term x →
              isDecomposableP-Term y →
              ({j : K} (e : SigEdge j k) → decomp x e ≡ decomp y e) → x ≡ y

        P0 :  ∀ {n₁ n₂} -> ∀ {ks₁ : Vec K (suc n₁)} {ks₂ : Vec K (suc n₂)} ->
             (s₁ : σ k ks₁) ->
             (s₂ : σ k ks₂) ->
             (ts  : TermsZ2 σ X ks₁) →
             (n₁ ≢-Str n₂) ->
             (i : Fin-R (suc n₂)) -> lookup-Term-try s₁ s₂ i ts ≡ failv
        P0 = {!!}

        P1 :   ∀ {n₁} -> ∀ {ks₁ : Vec K (suc n₁)}
             (s₁ : σ k ks₁) ->
             -- (s₂ : σ k ks₂) ->
             (ts  : TermsZ2 σ X ks₁) →
             (i : Fin-R (suc n₁)) -> lookup-Term-try s₁ s₁ i ts ≡ lookup-Term i ts
        P1 = {!!}

        failv≢var : ∀{x : X k} -> Path (TermZ2 σ X k) failv (var (right x)) -> 𝟘-𝒰
        failv≢var p with ≡→≡-Str p
        ... | ()

        compare : (x y : TermZ2 σ X k) ->
              isDecomposableP-Term x →
              isDecomposableP-Term y →
              (∑ λ j -> ∑ λ (e : SigEdge j k) -> decomp x e ≡ decomp y e -> 𝟘-𝒰) +-𝒰 (x ≡ y)
        compare (te {n₁} {ks₁} s₁ ts₁) (te {n₂} {ks₂} s₂ ts₂) (isTe s₁ ts₁) (isTe s₂ ts₂) with n₁ ≟-Str n₂
        ... | no ¬p = left (_ , (edge zero s₂) ,
                      λ p -> let Q1 = (P0 s₁ s₂ ts₁ ¬p zero ⁻¹)
                                 Q2 = isInjective:right p
                                 Q3 = P1 s₂ ts₂ zero
                             in {!!}
                      )
        ... | yes p = {!!}

        proof = {!!}


      -- | For this we take the following:
      RecAccessible:TermZ : IRecAccessible (Monad:TermZ2 σ)
      IRecAccessible.Dir RecAccessible:TermZ = of 𝑄
      IRecAccessible.ISet:Dir RecAccessible:TermZ = {!!}
      IRecAccessible.ISet:K RecAccessible:TermZ = {!!}
      IRecAccessible.IDiscreteStr:Dir RecAccessible:TermZ = {!!}
      IRecAccessible.IDiscreteStr:K RecAccessible:TermZ = {!!}
      ⟨ ⟨ IRecAccessible.decompose RecAccessible:TermZ ⟩ ⟩ = decomp
      INatural.naturality (of IRecAccessible.decompose RecAccessible:TermZ) f t i e = naturality-decomp f t e i
      IRecAccessible.commutes:decompose RecAccessible:TermZ t = {!!} -- lem-20.proof t e i
      IRecAccessible.δ-comm RecAccessible:TermZ f {j} {k} e x = lem-25.proof f e x
      ⟨ ⟨ IRecAccessible.pts RecAccessible:TermZ ⟩ ⟩ _ = failv
      INatural.naturality (of IRecAccessible.pts RecAccessible:TermZ) _ _ = refl
      IRecAccessible.a0 RecAccessible:TermZ = fail
      IRecAccessible.a0-adsorb RecAccessible:TermZ _ = refl
      IRecAccessible.k-a1 RecAccessible:TermZ = get-a1-k
      IRecAccessible.a1 RecAccessible:TermZ = get-a1 _
      IRecAccessible.isDecomposableP RecAccessible:TermZ = isDecomposableP-Term
      IRecAccessible.isPureP RecAccessible:TermZ = isPureP-Term
      IRecAccessible.decideDecompose RecAccessible:TermZ = decideDecompose-Term
      IRecAccessible.makeDec RecAccessible:TermZ = lem-30.proof
      IRecAccessible.makePure RecAccessible:TermZ = lem-40.proof
      IRecAccessible.isWellfounded::≺ RecAccessible:TermZ = {!!}
      IRecAccessible.cancel-δ RecAccessible:TermZ = lem-60.proof

{-
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
-}
