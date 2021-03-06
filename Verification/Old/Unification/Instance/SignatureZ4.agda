
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
  IDiscreteStr:Vec : β{A : π° π} {{_ : IDiscreteStr A}} -> IDiscreteStr (Vec A n)
  (IDiscreteStr:Vec IDiscreteStr.β-Str a) b = {!!}

  IDiscreteStr:β : IDiscreteStr β
  IDiscreteStr:β = {!!}

  ISet:β : ISet β
  ISet:β = {!!}

  ISet:Vec : β{A : π° π} {{_ : ISet A}} -> ISet (Vec A n)
  ISet:Vec = {!!}

  ISet:Fin-R : β{n} -> ISet (Fin-R n)
  ISet:Fin-R = {!!}

module _ {K : π°β} {{_ : IDiscreteStr K}} {{_ : ISet K}} where

  module _ (Ο : Signature) (isInhabited:Ο : isInhabited-Sig Ο) where
    private
      variable k : K
               ks : Vec K n
               -- j : K

    module _ {{_ : β{n k} {ks : Vec K (suc n)} -> IDiscreteStr (Ο k ks)}} where


      data isDecomposableP-Term {k : K} {X : K -> π°β} : Term Ο X k -> π°β where
        isTe : β{ks : Vec K (suc n)} -> (s : Ο k ks) -> {ts : Terms Ο X ks} -> (tsP : Termsα΅₯ ts) -> isDecomposableP-Term (te s ts tsP)
        isFail : isDecomposableP-Term fail

      data isPureP-Term {k : K} {X : K -> π°β} : Term Ο X k -> π°β where
        isVar : β(x : X k) -> isPureP-Term (var x)

      decideDecompose-Term : β{k} {X : K -> π°β} -> β (x : Term Ο X k) -> isPureP-Term x +-π° isDecomposableP-Term x
      decideDecompose-Term (te x xβ tsP) = right (isTe _ _)
      decideDecompose-Term (var x) = left (isVar _)
      decideDecompose-Term fail = right (isFail)


      data SigEdge : (a b : K) -> π°β where
        edge : β {k} {ks : Vec K (suc n)} -> (i : Fin-R (suc n)) -> Ο k ks -> SigEdge (lookup i ks) k
        fail : β{a : K} -> SigEdge a a

      get-a1-k : K -> K
      get-a1-k k =
        let _ , ks , _ = isInhabited:Ο k
        in lookup zero ks

      get-a1 : (k : K) -> SigEdge (get-a1-k k) k
      get-a1 k =
        let _ , ks , x = isInhabited:Ο k
        in edge zero x

      decide-e0-Term : β{k} {X : K -> π°β} -> (x : Term Ο X k) -> Decision (x β‘-Str fail)
      decide-e0-Term (te s ts tsP) = no (Ξ» ())
      decide-e0-Term (var x) = no (Ξ» ())
      decide-e0-Term fail = yes refl

      π : Quiver β₯
      β¨ π β© = K
      IQuiver.Edge (of π) = SigEdge
      IQuiver._β_ (of π) = _β‘_
      IQuiver.IEquivInst (of π) = IEquiv:Path

      -- compare-sig : β{k jβ jβ : K} -> {nβ nβ : β} -> (s )

      -- pattern failv = var (left (β₯ tt))

      module _ {V : K -> π°β} where
        lookup-Term : β{ks : Vec K (n)} -> (i : Fin-R (n)) -> Terms Ο V ks -> Term Ο V (lookup i ks)
        lookup-Term zero    (t β· ts) = t
        lookup-Term (suc i) (t β· ts) = lookup-Term i ts

        module lem-05 where
          proof : β{ks : Vec K (n)} -> (i : Fin-R (n)) -> (ts : Terms Ο V ks) -> lookup-Term i ts β-Terms ts
          proof zero (t β· ts) = this
          proof (suc i) (t β· ts) = t β· proof i ts

      module _ {V : K -> π°β} where
        lookup-Term-try : β{nβ nβ : β} {ksβ : Vec K (suc nβ)} {ksβ : Vec K (suc nβ)} (sβ : Ο k ksβ) (sβ : Ο k ksβ) (i : Fin-R (suc nβ)) (ts : Terms Ο V ksβ) -> (Term Ο V (lookup i ksβ))
        lookup-Term-try {nβ = nβ} {nβ} {ksβ} {ksβ} sβ sβ i ts with (nβ β-Str nβ)
        ... | no Β¬p = fail
        ... | yes refl-StrId with (ksβ β-Str ksβ)
        ... | no Β¬p = fail
        ... | yes refl-StrId with (sβ β-Str sβ)
        ... | no Β¬p = fail
        ... | yes refl-StrId = ((lookup-Term i ts))

        lookup-Term-try-β : β{nβ nβ : β} {ksβ : Vec K (suc nβ)} {ksβ : Vec K (suc nβ)} (sβ : Ο k ksβ) (sβ : Ο k ksβ) (i : Fin-R (suc nβ)) (ts : Terms Ο V ksβ) (tsP : Termsα΅₯ ts)
                          -> lookup-Term-try sβ sβ i (ts) β te sβ ts tsP

        lookup-Term-try-β {nβ = nβ} {nβ} {ksβ} {ksβ} sβ sβ i ts tsP with (nβ β-Str nβ)
        ... | no Β¬p = fail (Ξ» ())
        ... | yes refl-StrId with (ksβ β-Str ksβ)
        ... | no Β¬p = fail (Ξ» ())
        ... | yes refl-StrId with (sβ β-Str sβ)
        ... | no Β¬p = fail (Ξ» ())
        ... | yes refl-StrId = te (lem-05.proof i ts)


        eval-lookup-Term : β {nβ nβ} -> β{k} -> β {ksβ : Vec K (suc nβ)} {ksβ : Vec K (suc nβ)} ->
             (sβ : Ο k ksβ) ->
             (sβ : Ο k ksβ) ->
             (ts  : Terms Ο V ksβ) β
             (jβ : Fin-R (suc nβ))
             (jβ  : Fin-R (suc nβ))
             (pn : nβ β‘ nβ) ->
             (pks : PathP (Ξ» i -> Vec K (suc (pn i))) ksβ ksβ)
             (ps : PathP (Ξ» i -> Ο k (pks i)) sβ sβ)
              -> (pj : PathP (Ξ» i -> Fin-R (suc (pn i))) jβ jβ)
              -> PathP (Ξ» i -> Term Ο V (lookup (pj (~ i)) (pks (~ i)))) (lookup-Term-try sβ sβ jβ ts) (lookup-Term jβ ts)
        eval-lookup-Term {nβ} {nβ} {k} {ksβ} {ksβ} sβ sβ ts jβ jβ pn pks ps pj with (nβ β-Str nβ)
        ... | no Β¬p = π-rec (Β¬p (β‘ββ‘-Str pn))
        ... | yes refl-StrId with (ksβ β-Str ksβ) | β‘ββ‘-Str (hlevel {{ISet:β}} _ _ pn refl)
        ... | no Β¬p | refl-StrId = π-rec (Β¬p (β‘ββ‘-Str pks))
        ... | yes refl-StrId | refl-StrId with (sβ β-Str sβ) | β‘ββ‘-Str (hlevel {{ISet:Vec}} _ _ pks refl)
        ... | no Β¬p | refl-StrId = π-rec (Β¬p (β‘ββ‘-Str ps))
        ... | yes refl-StrId | refl-StrId with β‘ββ‘-Str pj
        ... | refl-StrId with β‘ββ‘-Str (hlevel {{ISet:Fin-R}} _ _ pj refl)
        ... | refl-StrId = refl


      module _ {X Y : K -> π°β} where
        naturality-lookup-Term : (f : β{k} -> X k -> Y k) -> β{ks : Vec K (n)} -> (i : Fin-R (n)) -> (ts : Terms Ο X ks) -> (map-Term f (lookup-Term i ts)) β‘ (lookup-Term i (map-Terms f ts))
        naturality-lookup-Term f zero (t β· ts) = refl
        naturality-lookup-Term f (suc i) (t β· ts) = naturality-lookup-Term f i ts

      module _ {V : K -> π°β} where
        commutes:lookup|join : β{ks : Vec K (n)} -> (i : Fin-R (n)) -> (ts : Terms Ο (Term Ο V) ks) -> (join-Term (lookup-Term i ts)) β‘ (lookup-Term i (join-Terms ts))
        commutes:lookup|join zero (t β· ts) = refl
        commutes:lookup|join (suc i) (t β· ts) = commutes:lookup|join i ts


      module _ {X Y : IdxSet K β₯} where
        naturality-lookup-Term-try : (f : X βΆ Y) {k : K} -> β {n nβ}
                                     -> β {ksβ : Vec K (suc n)} {ksβ : Vec K (suc nβ)} ->
                            -- (t : TermZ Ο X k) β
                            (sβ : Ο k ksβ) ->
                            (sβ : Ο k ksβ) ->
                            (ts  : Terms Ο (β¨ X β©) ksβ) β
                            (i : Fin-R (suc nβ)) ->
                            (map-Term β¨ f β©) (lookup-Term-try sβ sβ i ts) β‘
                                  lookup-Term-try sβ sβ i ((map-Terms β¨ f β© ts))
        naturality-lookup-Term-try f {k} {n} {nβ} {ksβ} {ksβ} sβ sβ ts i with (n β-Str nβ)
        ... | no Β¬p = refl
        ... | yes refl-StrId with (ksβ β-Str ksβ)
        ... | no Β¬p = refl
        ... | yes refl-StrId with (sβ β-Str sβ)
        ... | no Β¬p = refl
        ... | yes refl-StrId = naturality-lookup-Term β¨ f β© i ts
        -- naturality-lookup-Term β¨ f β© i (forget-Terms ts) β cong (lookup-Term i) (commutes:mapβ£forget-Terms β¨ f β© ts)


{-
      -- [Theorem]
      -- | The |Monad:TermZ| is recursively accessible.

-}


      -- | First we build the decomposition function:
      decomp : {k : K} {V : K -> π°β} -> Term Ο V k -> (β{j : K} -> SigEdge j k -> Maybe (Term Ο V j))
      decomp t fail = right fail
      -- decomp (te sβ ts tsP) (edge i sβ) = just (lookup-Term-try sβ sβ i (forget-Terms ts))
      decomp (te sβ ts tsP) (edge i sβ) = just (lookup-Term-try sβ sβ i ts)
      decomp (var xβ) (edge i x) = nothing
      decomp fail (edge i x) = right fail
      -- decomp t fail = right (failv)
      -- decomp ((te sβ ts)) (edge i sβ) = just (lookup-Term-try sβ sβ i ts)
      -- decomp (var v) (edge i x) = nothing

      module _ {X Y : IdxSet K β₯} where
        naturality-decomp : (f : X βΆ Y) {k : K}
                            (t : Term Ο (β¨ X β©) k) β
                            β{j} -> (e : SigEdge j k) ->
                            map-Maybe (map-Term β¨ f β©) (decomp t e) β‘ decomp (map-Term β¨ f β© t) e
        naturality-decomp f t fail = refl
        naturality-decomp f fail (edge i x) = refl
        naturality-decomp f (var xβ) (edge i x) = refl
        naturality-decomp f (te sβ ts tsP) (edge i sβ) = cong right (naturality-lookup-Term-try f sβ sβ ts i)
        -- cong right (naturality-lookup-Term-try f sβ sβ (forget-Terms ts) i)



      module lem-25 {X Y : K -> π°β} (f : β{k} -> X k βΆ Term Ο Y k) where
          proof : β{j k} -> β(e : Edge {{of π}} k j) -> β t -> (decomp t e β’ nothing) -> map-Maybe (Ξ» a β join-Term {V = Y} (map-Term f a)) (decomp t e)
                  β‘ decomp (join-Term {V = Y} (map-Term f t)) e

          P3 :             β {nβ} -> β {ksβ : Vec K (suc nβ)} ->
                            -- (t : TermZ Ο X k) β
                            (sβ : Ο k ksβ) ->
                            (ts  : Terms Ο X ksβ) β
                            (isFail-Terms (join-Terms (map-Terms f ts))) ->
                            -- (isFail-Terms (join-Termsα΅₯ (map-Termsα΅₯ f ts))) ->
                            (i : Fin-R (suc nβ)) ->
                            isFail-Term (join-Term (map-Term f (lookup-Term i ts)))
          P3 s ts F i =
            let t = lookup-Term i ts
                Q0 : t β-Terms ts
                Q0 = lem-05.proof i ts

                Q1 : map-Term f t β-Terms map-Terms f ts
                Q1 = mapβ-Terms f Q0

                Q2 : join-Term (map-Term f t) β-Terms join-Terms (map-Terms f ts)
                Q2 = joinβ-Terms Q1

            in failβ-Terms Q2 F


          P2 :             β {nβ nβ} -> β {ksβ : Vec K (suc nβ)} {ksβ : Vec K (suc nβ)} ->
                            (sβ : Ο k ksβ) ->
                            (sβ : Ο k ksβ) ->
                            (ts  : Terms Ο X ksβ) β
                            (i : Fin-R (suc nβ)) ->
                            (isFail-Terms (join-Terms (map-Terms f ts))) ->
                            (join-Term (map-Term f (lookup-Term-try sβ sβ i ts))) β‘ fail
          P2 {k} {nβ} {nβ} {ksβ} {ksβ} sβ sβ ts i F with (nβ β-Str nβ)
          ... | no Β¬p = refl
          ... | yes refl-StrId with (ksβ β-Str ksβ)
          ... | no Β¬p = refl
          ... | yes refl-StrId with (sβ β-Str sβ)
          ... | no Β¬p = refl
          ... | yes refl-StrId = cast::isFail-Term (P3 sβ ts F i)

          P4 :             β {nβ nβ} -> β {ksβ : Vec K (suc nβ)} {ksβ : Vec K (suc nβ)} ->
                            -- (t : TermZ Ο X k) β
                            (sβ : Ο k ksβ) ->
                            (sβ : Ο k ksβ) ->
                            (ts  : Terms Ο X ksβ) β
                            (i : Fin-R (suc nβ)) ->
                            -- (isFail-Terms (join-Termsα΅₯ (map-Termsα΅₯ f ts))) ->
                            (join-Term (map-Term f (lookup-Term-try sβ sβ i ts))) β‘ lookup-Term-try sβ sβ i (join-Terms (map-Terms f ts))
          P4 {k} {nβ} {nβ} {ksβ} {ksβ} sβ sβ ts i with (nβ β-Str nβ)
          ... | no Β¬p = refl
          ... | yes refl-StrId with (ksβ β-Str ksβ)
          ... | no Β¬p = refl
          ... | yes refl-StrId with (sβ β-Str sβ)
          ... | no Β¬p = refl
          ... | yes refl-StrId =
            let Q0 = join-Term (map-Term f (lookup-Term i ts)) β‘β¨ cong join-Term (naturality-lookup-Term f i ts) β©
                    join-Term (lookup-Term i (map-Terms f ts)) β‘β¨ commutes:lookup|join i _ β©
                    lookup-Term i (join-Terms (map-Terms f ts)) β
            in Q0



          proof fail t P = refl
          proof (edge i x) fail P = refl
          proof (edge i x) (var xβ) P = π-rec (P refl)
          proof (edge i sβ) (te sβ ts tsP) P with split-+-Str (reduce-Terms (join-Terms (map-Terms f ts)))
          ... | left (aF , P') = cong right (P2 sβ sβ ts i aF)
          ... | just ((ts') , P') = cong right (P4 sβ sβ ts i)



      module lem-30 {k} {X : K -> π°β} {x : Term Ο X k} where
        proof : isDecomposableP-Term x β {j : K} (e : SigEdge j k) β β (Ξ» y β decomp x e β‘-Str just y)
        proof (isTe s ts) (edge i x) = _ , refl
        proof (isTe s ts) fail = _ , refl
        proof isFail (edge i x) = _ , refl
        proof isFail fail = _ , refl

      module lem-40 {k} {X : K -> π°β} {x : Term Ο X k} where
        proof : isPureP-Term x β
              (decomp x (get-a1 k) β‘-Str nothing) Γ-π°
              ((β (Ξ» x' β x β‘-Str var x')))
        proof (isVar x) = refl , (_ , refl)


      module lem-60 {k} {X : K -> π°β} where
        proof : (x y : Term Ο X k) β
              isDecomposableP-Term x β
              isDecomposableP-Term y β
              ({j : K} (e : SigEdge j k) β decomp x e β‘ decomp y e) β x β‘ y

        P0 : β{k} -> {t s : Term Ο X k} -> isFail-Term t -> Β¬ isFail-Term s -> t β‘ s -> π-π°
        P0 fail sF p with β‘ββ‘-Str p
        ... | refl-StrId = sF fail

        P1 :  β {nβ nβ} -> β {ksβ : Vec K (suc nβ)} {ksβ : Vec K (suc nβ)} ->
             (sβ : Ο k ksβ) ->
             (sβ : Ο k ksβ) ->
             (ts  : Terms Ο X ksβ) β
             (nβ β’-Str nβ) ->
             (i : Fin-R (suc nβ)) -> isFail-Term (lookup-Term-try sβ sβ i ts)
        P1 {nβ} {nβ} {ksβ} {ksβ} sβ sβ ts pn i with (nβ β-Str nβ)
        ... | yes refl-StrId = π-rec (pn refl)
        ... | no Β¬p = fail

        P2 :  β {nβ nβ} -> β {ksβ : Vec K (suc nβ)} {ksβ : Vec K (suc nβ)} ->
             (sβ : Ο k ksβ) ->
             (sβ : Ο k ksβ) ->
             (ts  : Terms Ο X ksβ) β
             (pn : nβ β‘ nβ) ->
             (pks : PathP (Ξ» i -> Vec K (suc (pn i))) ksβ ksβ -> π-π°)
             (i : Fin-R (suc nβ)) -> isFail-Term (lookup-Term-try sβ sβ i ts)
        P2 {nβ} {nβ} {ksβ} {ksβ} sβ sβ ts pn pks i with (nβ β-Str nβ)
        ... | no Β¬p = fail
        ... | yes refl-StrId with (ksβ β-Str ksβ) | β‘ββ‘-Str (hlevel {{ISet:β}} _ _ pn refl)
        ... | no Β¬p | refl-StrId = fail
        ... | yes refl-StrId | refl-StrId = π-rec (pks refl)

        P3 :  β {nβ nβ} -> β {ksβ : Vec K (suc nβ)} {ksβ : Vec K (suc nβ)} ->
             (sβ : Ο k ksβ) ->
             (sβ : Ο k ksβ) ->
             (ts  : Terms Ο X ksβ) β
             (pn : nβ β‘ nβ) ->
             (pks : PathP (Ξ» i -> Vec K (suc (pn i))) ksβ ksβ)
             (ps : PathP (Ξ» i -> Ο k (pks i)) sβ sβ -> π-π°)
             (i : Fin-R (suc nβ)) -> isFail-Term (lookup-Term-try sβ sβ i ts)
        P3 {nβ} {nβ} {ksβ} {ksβ} sβ sβ ts pn pks ps i with (nβ β-Str nβ)
        ... | no Β¬p = fail
        ... | yes refl-StrId with (ksβ β-Str ksβ) | β‘ββ‘-Str (hlevel {{ISet:β}} _ _ pn refl)
        ... | no Β¬p | refl-StrId = fail
        ... | yes refl-StrId | refl-StrId with (sβ β-Str sβ) | β‘ββ‘-Str (hlevel {{ISet:Vec}} _ _ pks refl)
        ... | no Β¬p | refl-StrId = fail -- π-rec (Β¬p (β‘ββ‘-Str ps))
        ... | yes refl-StrId | refl-StrId = π-rec (ps refl) -- nofailEdge ts


        P4 : β{ks : Vec K (n)} -> (tsβ tsβ : Terms Ο X ks) -> (β i -> lookup-Term i tsβ β‘ lookup-Term i tsβ) -> tsβ β‘ tsβ
        P4 [] [] _ = refl
        P4 (t β· ts) (s β· ss) P i = P zero i β· P4 ts ss (Ξ» j -> P (suc j)) i


        -- P1 :   β {nβ} -> β {ksβ : Vec K (suc nβ)}
        --      (sβ : Ο k ksβ) ->
        --      -- (sβ : Ο k ksβ) ->
        --      (ts  : TermsZ2 Ο X ksβ) β
        --      (i : Fin-R (suc nβ)) -> lookup-Term-try sβ sβ i ts β‘ lookup-Term i ts
        -- P1 = {!!}

        -- failvβ’var : β{x : X k} -> Path (TermZ2 Ο X k) failv (var (right x)) -> π-π°
        -- failvβ’var p with β‘ββ‘-Str p
        -- ... | ()

        nofailEdge : β{ks : Vec K n} -> {ts : Terms Ο X ks} -> (tsP : Termsα΅₯ ts) -> β Ξ» j -> Β¬ isFail-Term (lookup-Term j (ts))
        nofailEdge (te s tsβ tsP β· ts) = zero , Ξ» {()}
        nofailEdge (var x β· ts) = zero , Ξ» {()}
        nofailEdge (failβ· tsP) = let j , jF = nofailEdge tsP in suc j , jF
        -- nofailEdge (te s tsβ β· ts) = zero , Ξ» {()}
        -- nofailEdge (var x β· ts) = zero , Ξ» {()}
        -- nofailEdge (failβ· ts) = let j , jF = nofailEdge ts in suc j , jF


        nofailEdge2 :  β {nβ nβ} -> β {ksβ : Vec K (suc nβ)} {ksβ : Vec K (suc nβ)} ->
             (sβ : Ο k ksβ) ->
             (sβ : Ο k ksβ) ->
             {ts  : Terms Ο X ksβ} β
             (tsP : Termsα΅₯ ts)
             (pn : nβ β‘ nβ) ->
             (pks : PathP (Ξ» i -> Vec K (suc (pn i))) ksβ ksβ)
             (ps : PathP (Ξ» i -> Ο k (pks i)) sβ sβ)
              -> β Ξ» j -> Β¬ isFail-Term (lookup-Term-try sβ sβ j ts)
        nofailEdge2 {nβ} {nβ} {ksβ} {ksβ} sβ sβ ts pn pks ps with (nβ β-Str nβ)
        ... | no Β¬p = π-rec (Β¬p (β‘ββ‘-Str pn))
        ... | yes refl-StrId with (ksβ β-Str ksβ) | β‘ββ‘-Str (hlevel {{ISet:β}} _ _ pn refl)
        ... | no Β¬p | refl-StrId = π-rec (Β¬p (β‘ββ‘-Str pks))
        ... | yes refl-StrId | refl-StrId with (sβ β-Str sβ) | β‘ββ‘-Str (hlevel {{ISet:Vec}} _ _ pks refl)
        ... | no Β¬p | refl-StrId = π-rec (Β¬p (β‘ββ‘-Str ps))
        ... | yes refl-StrId | refl-StrId = nofailEdge ts

        compare : (x y : Term Ο X k) ->
              isDecomposableP-Term x β
              isDecomposableP-Term y β
              ({j : K} (e : SigEdge j k) β decomp x e β‘ decomp y e) ->
              (β Ξ» j -> β Ξ» (e : SigEdge j k) -> decomp x e β‘ decomp y e -> π-π°) +-π° (x β‘ y)
        compare (fail) (te {nβ} {ksβ} sβ tsβ tsPβ) (isFail) (isTe sβ tsPβ) Pd =
          let j , Fj = nofailEdge2 sβ sβ tsPβ refl refl refl
          in left (_ , edge j sβ ,
                  Ξ» p -> let Q1 = isInjective:right p
                             Q2 = fail
                         in P0 Q2 Fj Q1
                  )
        compare (te {nβ} {ksβ} sβ tsβ tsPβ) (fail) (isTe sβ tsPβ) (isFail) Pd =
          let j , Fj = nofailEdge2 sβ sβ tsPβ refl refl refl
          in left (_ , edge j sβ ,
                  Ξ» p -> let Q1 = isInjective:right p
                             Q2 = fail
                         in P0 Q2 Fj (sym Q1)
                  )
        compare fail fail isFail isFail Pd = right refl
        compare (te {nβ} {ksβ} sβ tsβ tsPβ) (te {nβ} {ksβ} sβ tsβ tsPβ) (isTe sβ tsPβ) (isTe sβ tsPβ) Pd with nβ β-Str nβ
        ... | no Β¬p =
          let j , Fj = nofailEdge2 sβ sβ tsPβ refl refl refl
          in left (_ , edge j sβ ,
                  Ξ» p -> let Q1 = isInjective:right p
                             Q2 = P1 sβ sβ (tsβ) Β¬p j
                         in P0 Q2 Fj Q1
                  )
        ... | yes refl-StrId with (ksβ β-Str ksβ)
        ... | no Β¬p =
          let j , Fj = nofailEdge2 sβ sβ tsPβ refl refl refl
          in left (_ , edge j sβ ,
                  Ξ» p -> let Q1 = isInjective:right p
                             Q2 = P2 sβ sβ (tsβ) refl (Ξ» {p -> Β¬p (β‘ββ‘-Str p)}) j
                         in P0 Q2 Fj Q1
                  )
        ... | yes refl-StrId with (sβ β-Str sβ)
        ... | no Β¬p =
          let j , Fj = nofailEdge2 sβ sβ tsPβ refl refl refl
          in left (_ , edge j sβ ,
                  Ξ» p -> let Q1 = isInjective:right p
                             Q2 = P3 sβ sβ tsβ refl refl (Ξ» {p -> Β¬p (β‘ββ‘-Str p)}) j
                         in P0 Q2 Fj Q1
                  )
        ... | yes refl-StrId =
             let Q0 : (j : Fin-R (suc nβ)) β lookup-Term j tsβ β‘ lookup-Term j tsβ
                 Q0 j = eval-lookup-Term sβ sβ (tsβ) j j refl refl refl refl β»ΒΉ
                        β isInjective:right (Pd (edge j sβ))
                        β eval-lookup-Term sβ sβ (tsβ) j j refl refl refl refl
                 Q1 : tsβ β‘ tsβ
                 Q1 = P4 tsβ tsβ Q0
                 Q2 : Path (β Termsα΅₯) (tsβ , tsPβ) (_ , tsPβ)
                 Q2 = byFirstP Q1
              -- Q2 = β‘-Strββ‘ (isInjective:forget-Terms (β‘ββ‘-Str Q1))
        --   in right (Ξ» i -> te sβ (Q2 i))
            in right (Ξ» i -> te sβ (Q2 i .fst) (Q2 i .snd))

        proof x y Px Py Pd with compare x y Px Py Pd
        ... | left (j , e , Β¬Pd) = π-rec (Β¬Pd (Pd e))
        ... | just p = p

      module lem-70 {X : K -> π°β} where
        proof : β{k j} -> (x : Term Ο X k) -> (y : Term Ο X j)
                    β (y β’-Str fail) Γ-π° (β (Ξ» e β decomp y e β‘-Str just x))
              -> x β y
        proof .(lookup-Term-try s xβ i (ts)) (te s ts tsP) (P , edge i xβ , refl-StrId) = lookup-Term-try-β s xβ i ts tsP
        proof .fail (te s ts tsP) (P , fail , refl-StrId) = fail P
        proof .fail (var xβ) (P , fail , refl-StrId) = fail P
        proof x fail (P , Q) = π-rec (P refl)


      -- | For this we take the following:
      RecAccessible:TermZ : IRecAccessible (Monad:Term Ο)
      IRecAccessible.Dir RecAccessible:TermZ = of π
      IRecAccessible.ISet:Dir RecAccessible:TermZ = {!!}
      IRecAccessible.ISet:K RecAccessible:TermZ = {!!}
      IRecAccessible.IDiscreteStr:Dir RecAccessible:TermZ = {!!}
      IRecAccessible.IDiscreteStr:K RecAccessible:TermZ = {!!}
      β¨ β¨ IRecAccessible.decompose RecAccessible:TermZ β© β© = decomp
      INatural.naturality (of IRecAccessible.decompose RecAccessible:TermZ) f t i e = naturality-decomp f t e i
      -- IRecAccessible.commutes:decompose RecAccessible:TermZ t = {!!} -- lem-20.proof t e i
      IRecAccessible.Ξ΄-comm RecAccessible:TermZ f {j} {k} e x = lem-25.proof β¨ f β© e x
      -- β¨ β¨ IRecAccessible.pts RecAccessible:TermZ β© β© _ = fail -- failv
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
      IRecAccessible._βΊP_ RecAccessible:TermZ (x) (y) = x .snd β y .snd
      IRecAccessible.recreate-βΊ RecAccessible:TermZ = lem-70.proof _ _
      IRecAccessible.isWellfounded::βΊP RecAccessible:TermZ = isWellfounded::β
      IRecAccessible.cancel-Ξ΄ RecAccessible:TermZ = lem-60.proof


