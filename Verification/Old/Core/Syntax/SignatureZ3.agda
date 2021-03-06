
module Verification.Old.Core.Syntax.SignatureZ3 where

open import Verification.Conventions hiding (k)
open import Verification.Old.Core.Category
open import Verification.Old.Core.Order
open import Verification.Old.Core.Type
open import Verification.Old.Core.Category.Monad
open import Verification.Old.Core.Category.Instance.Kleisli
open import Verification.Old.Core.Category.Instance.IdxSet
open import Verification.Old.Core.Category.Limit.Specific
open import Verification.Old.Core.Category.Limit.Kan
-- open import Verification.Unification.RecAccessible


module _ {K : π°β} where
  -- Symbol : π°β
  -- Symbol = β Ξ» (n : β) -> K Γ-π° (Vec K n)

  Signature : π°β
  Signature = {n : β} -> K -> Vec K (suc n) -> π°β

  isInhabited-Sig : Signature -> π°β
  isInhabited-Sig Ο = β k -> β Ξ» n -> β Ξ» (ks : Vec K (suc n)) -> Ο k ks

  data TermO (Ο : Signature) (V : K -> π°β) (k : K) : π°β
  data TermsO (Ο : Signature) (V : K -> π°β) : {n : β} (ks : Vec K n) -> π°β where
    [] : TermsO Ο V []
    _β·_ : β{k} {ks : Vec K n} -> (t : TermO Ο V k) -> (ts : TermsO Ο V ks) -> TermsO Ο V (k β· ks)

  data TermO Ο V k where
    te : β{ks : Vec K (suc n)} -> (s : Ο k ks) -> (ts : TermsO Ο V ks) -> TermO Ο V k
    var : V k -> TermO Ο V k
    fail : TermO Ο V k

  data Term (Ο : Signature) (V : K -> π°β) (k : K) : π°β
  data Terms (Ο : Signature) (V : K -> π°β) : {n : β} (ks : Vec K n) -> π°β where
    [] : Terms Ο V []
    _β·_ : β{k} {ks : Vec K n} -> (t : Term Ο V k) -> (ts : Terms Ο V ks) -> Terms Ο V (k β· ks)

  -- data isNotFail-Term {Ο : Signature} {V : K -> π°β} : {k : K} -> Term Ο V k -> π°β where
  data Termα΅₯ (Ο : Signature) (V : K -> π°β) (k : K) : π°β

  -- data isNotFail-Terms {Ο : Signature} {V : K -> π°β} : {n : β} {ks : Vec K n} -> Terms Ο V ks -> π°β
  data Termsα΅₯ (Ο : Signature) (V : K -> π°β) : {n : β} (ks : Vec K n) -> π°β

  data Term Ο V k where
    te : β{ks : Vec K (suc n)} -> (s : Ο k ks) -> (ts : Termsα΅₯ Ο V ks) -> Term Ο V k
    var : V k -> Term Ο V k
    fail : Term Ο V k

  data Termsα΅₯ Ο V where
    _β·_ : {k : K} -> (Termα΅₯ Ο V k) -> β{n} -> {ks : Vec K n} -> (ts : Terms Ο V ks) -> Termsα΅₯ Ο V (k β· ks)
    failβ·_ : {k : K} -> {ks : Vec K n} -> (ts : Termsα΅₯ Ο V ks) -> Termsα΅₯ Ο V (k β· ks)

  data Termα΅₯ Ο V k where
    te : β{ks : Vec K (suc n)} -> (s : Ο k ks) -> (ts : Termsα΅₯ Ο V ks) -> Termα΅₯ Ο V k
    var : V k -> Termα΅₯ Ο V k


  module _ {Ο : Signature} {V : K -> π°β} where
    forget-Term : β{k} -> Termα΅₯ Ο V k -> Term Ο V k
    forget-Term (te s ts) = te s ts
    forget-Term (var x) = var x

    forget-Terms : {ks : Vec K n} -> Termsα΅₯ Ο V ks -> Terms Ο V ks
    forget-Terms (x β· ts) = forget-Term x β· ts
    forget-Terms (failβ· ts) = fail β· forget-Terms ts

    split:β·α΅₯ : {k : K} -> {t s : Termα΅₯ Ο V k} -> β{n} -> {ks : Vec K n} -> {u v : Terms Ο V ks}
            -> StrId {A = Termsα΅₯ Ο V (k β· ks)} (t β· u) (s β· v) -> (t β‘-Str s) Γ-π° (u β‘-Str v)
    split:β·α΅₯ refl-StrId = refl , refl

    split:β· : {k : K} -> {t s : Term Ο V k} -> β{n} -> {ks : Vec K n} -> {u v : Terms Ο V ks}
            -> StrId {A = Terms Ο V (k β· ks)} (t β· u) (s β· v) -> (t β‘-Str s) Γ-π° (u β‘-Str v)
    split:β· refl-StrId = refl , refl

    isInjective:forget-Term : β{k} -> {t s : Termα΅₯ Ο V k} -> forget-Term t β‘-Str forget-Term s -> t β‘-Str s
    isInjective:forget-Term {t = te sβ ts} {te .sβ .ts} refl-StrId = refl-StrId
    isInjective:forget-Term {t = var x} {var .x} refl-StrId = refl-StrId

    isInjective:forget-Terms : {ks : Vec K n} -> {t s : Termsα΅₯ Ο V ks} -> forget-Terms t β‘-Str forget-Terms s -> t β‘-Str s
    isInjective:forget-Terms {t = x β· ts} {xβ β· tsβ} p with split:β· p
    ... | p1 , refl-StrId with isInjective:forget-Term p1
    ... | refl-StrId = refl
    isInjective:forget-Terms {t = x β· ts} {failβ· s} p with split:β· p
    isInjective:forget-Terms {suc _} {_ β· _} {te sβ tsβ β· ts} {failβ· s} p | () , p2
    isInjective:forget-Terms {suc _} {_ β· _} {var x β· ts} {failβ· s} p | () , p2
    isInjective:forget-Terms {t = failβ· t} {x β· ts} p with split:β· p
    isInjective:forget-Terms {suc _} {_ β· _} {failβ· t} {te s tsβ β· ts} p | () , p2
    isInjective:forget-Terms {suc _} {_ β· _} {failβ· t} {var x β· ts} p | () , p2
    isInjective:forget-Terms {t = failβ· t} {failβ· s} p with split:β· p
    ... | p1 , p2 with isInjective:forget-Terms p2
    ... | refl-StrId = refl-StrId

  module _ {Ο : Signature} {V : K -> π°β} where
    data isFail-Term {k : K} : (Term Ο V k) -> π°β where
      fail : isFail-Term fail

    cast::isFail-Term : {k : K} -> {t : Term Ο V k} -> isFail-Term t -> t β‘ fail
    cast::isFail-Term fail = refl

    data isFail-Terms : {n : β} {ks : Vec K n} -> (ts : Terms Ο V ks) -> π°β where
      [] : isFail-Terms []
      _β·_ : β{k} -> {t : Term Ο V k} -> (isFail-Term t) -> {n : β} {ks : Vec K n} -> {ts : Terms Ο V ks} -> isFail-Terms ts -> isFail-Terms (t β· ts)

    data _β-Terms_ : {k : K} -> β{n} -> {ks : Vec K n} -> (t : Term Ο V k) -> (ts : Terms Ο V ks) -> π°β where
      this : {k : K} -> {t : Term Ο V k} -> β{n} -> {ks : Vec K n} -> {ts : Terms Ο V ks} -> t β-Terms (t β· ts)
      _β·_ : {kβ kβ : K} -> {tβ : Term Ο V kβ} -> (tβ : Term Ο V kβ)-> β{n} -> {ks : Vec K n} -> {ts : Terms Ο V ks} -> tβ β-Terms ts -> tβ β-Terms (tβ β· ts)

    -- data _β-Termsα΅₯_ : {k : K} -> β{n} -> {ks : Vec K n} -> (t : Term Ο V k) -> (ts : Termsα΅₯ Ο V ks) -> π°β where
    --   this : {k : K} -> (t : Termα΅₯ Ο V k) -> (t' : Term Ο V k) -> (forget-Term t β‘-Str t') -> β{n} -> {ks : Vec K n} -> {ts : Terms Ο V ks} -> t' β-Termsα΅₯ (t β· ts)
    --   older : {kβ kβ : K} -> {tβ : Term Ο V kβ} -> (tβ : Termα΅₯ Ο V kβ) -> β{n} -> {ks : Vec K n} -> {ts : Terms Ο V ks} -> tβ β-Terms ts -> tβ β-Termsα΅₯ (tβ β· ts)
    --   failβ·_ : β {k} -> {kβ : K} -> {tβ : Term Ο V kβ} -> β{n} -> {ks : Vec K n} -> {ts : Termsα΅₯ Ο V ks} -> tβ β-Termsα΅₯ ts -> tβ β-Termsα΅₯ (failβ·_ {k = k} ts)

    data _β_ : {kβ kβ : K} -> (tβ : Term Ο V kβ) -> (tβ : Term Ο V kβ) -> π°β where
      te : {k j : K} -> {t : Term Ο V k} -> β{n} -> {ks : Vec K (suc n)} -> {s : Ο j ks} -> {ts : Termsα΅₯ Ο V ks} -> (t β-Terms (forget-Terms ts)) -> t β te s (ts)
      fail : β{k j : K} -> {t : Term Ο V k} -> (t β’-Str fail) -> fail {k = j} β t

    -- data _β-TermsO_ : {k : K} -> β{n} -> {ks : Vec K n} -> (t : TermO Ο V k) -> (ts : TermsO Ο V ks) -> π°β where
    --   this : {k : K} -> {t : TermO Ο V k} -> β{n} -> {ks : Vec K n} -> {ts : TermsO Ο V ks} -> t β-TermsO (t β· ts)
    --   _β·_ : {kβ kβ : K} -> {tβ : TermO Ο V kβ} -> (tβ : TermO Ο V kβ)-> β{n} -> {ks : Vec K n} -> {ts : TermsO Ο V ks} -> tβ β-TermsO ts -> tβ β-TermsO (tβ β· ts)

    -- data _βO_ : {kβ kβ : K} -> (tβ : TermO Ο V kβ) -> (tβ : TermO Ο V kβ) -> π°β where
    --   te : {k : K} -> {t : TermO Ο V k} -> β{n} -> {ks : Vec K (suc n)} -> {s : Ο k ks} -> {ts : TermsO Ο V ks} -> (t β-TermsO ts) -> t βO te s (ts)

    _β'_ : (t s : β Term Ο V) -> π°β
    _β'_ (_ , t) (_ , s) = t β s

    depth-Term : β{k} -> Term Ο V k -> β
    depth-Terms : β{ks : Vec K n} -> Terms Ο V ks -> Vec β n
    depth-Termα΅₯ : β{k} -> Termα΅₯ Ο V k -> β
    depth-Termsα΅₯ : β{ks : Vec K n} -> Termsα΅₯ Ο V ks -> Vec β n

    depth-Termα΅₯ (te s ts) = suc (β (depth-Termsα΅₯ ts))
    depth-Termα΅₯ (var x) = 0

    depth-Termsα΅₯ (t β· ts) = depth-Termα΅₯ t β· depth-Terms ts
    depth-Termsα΅₯ (failβ· ts) = 0 β· depth-Termsα΅₯ ts

    depth-Terms [] = []
    depth-Terms (t β· ts) = depth-Term t β· depth-Terms ts

    depth-Term (te s ts) = suc (β (depth-Termsα΅₯ ts))
    depth-Term (var x) = 0
    depth-Term fail = 0

    depth-forget : β{k} -> (t : Termα΅₯ Ο V k) -> depth-Term (forget-Term t) β‘ depth-Termα΅₯ t
    depth-forget (te s ts) = refl
    depth-forget (var x) = refl

    depth-β-Terms : {k : K} -> β{n} -> {ks : Vec K n} -> {t : Term Ο V k} -> {ts : Terms Ο V ks}
                    -> t β-Terms ts -> depth-Term t β€ β (depth-Terms ts)
    depth-β-Terms {ts = .(_ β· _)} this = ΞΉβ-β¨ {A = β}
    depth-β-Terms {ts = .(tβ β· _)} (tβ β· x) = trans-β€ {A = β} (depth-β-Terms x) (ΞΉβ-β¨ {A = β} {a = depth-Term tβ})

    depth-β-Termsα΅₯ : {k : K} -> β{n} -> {ks : Vec K n} -> {t : Term Ο V k} -> {ts : Termsα΅₯ Ο V ks}
                    -> t β-Terms (forget-Terms ts) -> depth-Term t β€ β (depth-Termsα΅₯ ts)
    depth-β-Termsα΅₯ {ts = t β· ts} this = trans-β€ {A = β} (0 , depth-forget t) (ΞΉβ-β¨ {A = β})
    depth-β-Termsα΅₯ {ts = xβ β· ts} (.(forget-Term xβ) β· x) = trans-β€ {A = β} (depth-β-Terms x) (ΞΉβ-max {a = depth-Termα΅₯ xβ})
    depth-β-Termsα΅₯ {ts = failβ· ts} this = zero-β€
    depth-β-Termsα΅₯ {ts = failβ· ts} (.fail β· x) = trans-β€ {A = β} (depth-β-Termsα΅₯ x) (ΞΉβ-max {a = 0})


    -- depth-β-Termsα΅₯ {ts = .(t β· _)} (this t _ x) = {!!}
    -- depth-β-Termsα΅₯ {ts = .(tβ β· _)} (older tβ x) = {!!}
    -- depth-β-Termsα΅₯ {ts = .(failβ· _)} (failβ· P) = {!!}

    private

      -- lem-10-Terms : β{n} {ks : Vec K n} -> (x : Terms Ο V ks) -> Acc (_β'_) (_ , x)

      lem-10 : β{k} -> (x : Term Ο V k) -> (n : β) -> (depth-Term x β€ n) -> Acc (_β'_) (_ , x)
      lem-10 (te s ts) zero P = π-rec (Β¬-<-zero P)
      lem-10 (te s ts) (suc n) P =
        acc (Ξ» { (k , t') (te x) β lem-10 t' n (trans-β€ {A = β} (depth-β-Termsα΅₯ x) (pred-β€-pred P))
               ;  (fstβ , .fail) (fail a) β acc (Ξ» { (fstβ , .fail) (fail x) β π-rec (x refl)})
               })

      lem-10 (var x) n P = acc (Ξ» { (fstβ , .fail) (fail a) β acc (Ξ» { (fstβ , .fail) (fail x) β π-rec (x refl)})})
      lem-10 fail n P = acc (Ξ» { (fstβ , .fail) (fail a) β acc (Ξ» { (fstβ , .fail) (fail x) β π-rec (x refl)})})
      -- acc (Ξ» {x y -> {!!}})

      -- lem-10 (t) = acc (Ξ» { (k , sndβ) (te (this t .sndβ x)) β {!!}
      --                     ; (k , sndβ) (te (older tβ x)) β {!!}
      --                     ; (k , sndβ) (te (failβ· x)) β {!!}})

      -- lem-10 (te s (failβ· ts)) = acc (Ξ» { (fst , .fail) (te this) β lem-10 fail
      --                                   ; (fst , sndβ) (te (.fail β· x)) β {!!}})
      -- -- acc (Ξ» { (_ , t') (te x) β {!!}})
      -- lem-10 (var x) = acc (Ξ» { y ()})
      -- lem-10 (fail) = acc (Ξ» { y ()})

    isWellfounded::β : WellFounded (Ξ» (x y : β Term Ο V) -> x .snd β y .snd)
    isWellfounded::β (_ , x) = lem-10 x (depth-Term x) refl-β€-β

    {-

    _βO'_ : (t s : β TermO Ο V) -> π°β
    _βO'_ (_ , t) (_ , s) = t βO s

    private
      -- lem-20-Terms : β{n} -> β{ks : Vec K n} -> (x : TermsO Ο V ks) -> Acc (_)
      -- {-# INLINE lem-20 #-}

      postulate
        use : β{A B : π°β} -> A -> B
      -- use = {!!}
      acc-te : β{n}-> β{ks : Vec K (suc n)} -> (ts : TermsO Ο V ks) -> (β{k} (t : TermO Ο V k)
             -> t β-TermsO ts -> Acc (_βO'_) (_ , t)) -> β {j} -> β(s : Ο j (ks)) -> Acc (_βO'_) (_ , te s ts)
      acc-te = {!!}

      lem-20 : β{k} -> (x : TermO Ο V k) -> Acc (_βO'_) (_ , x)

      lem-21 : β{n}-> β{ks : Vec K n} -> (ts : TermsO Ο V ks) -> β{k} (t : TermO Ο V k) -> t β-TermsO ts -> Acc (_βO'_) (_ , t)
      lem-21 .(t β· _) t this = lem-20 t
      lem-21 .(tβ β· _) t (tβ β· p) = {!!}
      -- lem-21 .(t β· _) t this = 
      -- lem-21 .(tβ β· _) t (tβ β· p) = lem-21 t _ p

      -- lem-20 (te s ts) = acc-te ts (lem-21 ts) s
      lem-20 (te s (t β· [])) = use (lem-20 t)
      lem-20 (te s (t β· (tβ β· ts))) = {!!}
      lem-20 (var x) = acc (Ξ» { y ()})
      lem-20 fail = acc (Ξ» { y ()})

      {-# INLINE lem-21 #-}
      -}

      -- lem-20 (te s (t β· [])) = use f -- acc (Ξ» { (_ , t') (te this) β f})
      --   where f = lem-20 t
      -- lem-20 (te s (t β· (tβ β· ts))) = {!!}
      -- -- acc (Ξ» {y (te x) β lem-21 _ ts x})
      -- lem-20 (var x) = acc (Ξ» { y ()})
      -- lem-20 fail = acc (Ξ» { y ()})

      -- lem-20 (te s ts) = acc (Ξ» {y (te x) β lem-21 _ ts x})
      -- lem-20 (var x) = acc (Ξ» { y ()})
      -- lem-20 fail = acc (Ξ» { y ()})



      -- acc (Ξ» { (k , t') (te this) β {!!}
      --                   ; (k , t') (te (tβ β· x)) β {!!}})
      {-
    forget-O-Terms : β{n} -> {ks : Vec K n} -> Termsα΅₯ Ο V ks -> TermsO Ο V ks
    forget-O-Terms (x β· ts) = {!!}
    forget-O-Terms (failβ· ts) = {!!}

    forget-O-Term : β{k} -> Term Ο V k -> TermO Ο V k
    forget-O-Term (te s ts) = te s (forget-O-Terms ts)
    forget-O-Term (var x) = var x
    forget-O-Term fail = fail

    acc-O : β{k} -> β(x : Term Ο V k) -> Acc _βO'_ (_ , forget-O-Term x) -> Acc _β'_ (_ , x)
    acc-O (te s ts) A = {!!}
    acc-O (var x) A = {!!}
    acc-O fail A = {!!}

    isWellfounded::βO : WellFounded (Ξ» (x y : β TermO Ο V) -> x βO' y)
    isWellfounded::βO (_ , x) = {!!}
    -}


    -- (_ , te s ts) = {!!}
    -- isWellfounded::β (_ , var x) = {!!}
    -- isWellfounded::β (_ , fail) = {!!}
-- acc (Ξ» {(_ , y) yβx -> {!!}})

    failβ-Terms : {k : K} -> β{n} -> {ks : Vec K n} -> {t : Term Ο V k} -> {ts : Terms Ο V ks}
                -> t β-Terms ts -> isFail-Terms ts -> isFail-Term t
    failβ-Terms this (x β· F) = x
    failβ-Terms (tβ β· P) (x β· F) = failβ-Terms P F


    join-Term : {k : K} -> Term Ο (Term Ο V) k -> Term Ο V k
    join-Termα΅₯ : {k : K} -> Termα΅₯ Ο (Term Ο V) k -> Term Ο V k

    join-Terms : {ks : Vec K n} -> Terms Ο (Term Ο V) ks -> Terms Ο V ks
    join-Terms [] = []
    join-Terms (t β· ts) = join-Term t β· join-Terms ts

    join-Termsα΅₯ : {ks : Vec K n} -> Termsα΅₯ Ο (Term Ο V) ks -> Terms Ο V ks
    join-Termsα΅₯ (t β· ts) = join-Termα΅₯ t β· join-Terms ts
    join-Termsα΅₯ (failβ· ts) = fail β· join-Termsα΅₯ ts

    reduce-Term : β{k} -> (t : Term Ο V k) -> isFail-Term t +-π° (β Ξ» (t' : Termα΅₯ Ο V k) -> forget-Term t' β‘ t)
    reduce-Term (te s ts) = right (te s ts , refl)
    reduce-Term (var x) = right (var x , refl)
    reduce-Term fail = left fail

    reduce-Terms : {ks : Vec K n} -> (ts : Terms Ο V ks) -> (isFail-Terms ts) +-π° (β Ξ» (ts' : Termsα΅₯ Ο V ks) -> forget-Terms ts' β‘ ts)
    reduce-Terms [] = left []
    reduce-Terms (t β· ts) with reduce-Term t
    ... | just (t' , t'P) = right (t' β· ts , Ξ» i -> t'P i β· ts)
    ... | left fail with reduce-Terms ts
    ... | left (ts'F) = left (fail β· ts'F)
    ... | just (ts' , ts'P) = right (failβ· ts' , Ξ» i -> fail β· ts'P i)

    join-te : β{k} {ks : Vec K (suc n)} -> Ο k ks -> Terms Ο V ks -> Term Ο V k
    join-te s ts with split-+-Str (reduce-Terms ts)
    ... | left (_ , _) = fail
    ... | just ((ts' , _) , _) = te s ts'

    join-Termα΅₯ (te s ts) = join-te s (join-Termsα΅₯ ts)
    join-Termα΅₯ (var x) = x

    join-Term (te s ts) = join-te s (join-Termsα΅₯ ts)
    join-Term (var t) = t
    join-Term fail = fail

  module _ {Ο : Signature} {V : K -> π°β} where
    joinβ-Terms : {ks : Vec K n} -> β{k} -> {t : Term Ο (Term Ο V) k} {ts : Terms Ο (Term Ο V) ks} -> t β-Terms ts -> join-Term t β-Terms join-Terms ts
    joinβ-Terms {t = t} {.(t β· _)} this = this
    joinβ-Terms {t = t} {.(tβ β· _)} (tβ β· P) = _ β· joinβ-Terms P

    split:joinβ£forget-Term : β{k} -> (t : Termα΅₯ Ο (Term Ο V) k) -> join-Termα΅₯ t β‘ join-Term (forget-Term t)
    split:joinβ£forget-Term (te s ts) = refl
    split:joinβ£forget-Term (var x) = refl

    split:joinβ£forget-Terms : {ks : Vec K n} -> (ts : Termsα΅₯ Ο (Term Ο V) ks) -> join-Termsα΅₯ ts β‘ join-Terms (forget-Terms ts)
    split:joinβ£forget-Terms (t β· ts) i = split:joinβ£forget-Term t i β· join-Terms ts
    split:joinβ£forget-Terms (failβ· ts) i = fail β· split:joinβ£forget-Terms ts i

    reduce-isFail-Term : β{k} -> {t : Term Ο V k} -> isFail-Term t -> β Ξ» x -> reduce-Term t β‘-Str left x
    reduce-isFail-Term fail = _ , refl

    reduce-isFail-Terms : {ks : Vec K n} -> {ts : Terms Ο V ks} -> isFail-Terms ts -> β Ξ» x -> reduce-Terms ts β‘-Str left x
    reduce-isFail-Terms {ts = .[]} [] = _ , refl
    reduce-isFail-Terms {ts = (t β· ts)} (x β· P) with reduce-Term t | reduce-isFail-Term x
    ... | left fail | .fail , refl-StrId with reduce-Terms ts | reduce-isFail-Terms P
    ... | left xβ | Y = _ , refl


  module _ (Ο : Signature) where
    IdxTerm : IdxSet K ββ -> IdxSet K ββ
    β¨ IdxTerm V β© = Term Ο β¨ V β©
    of (IdxTerm V) = {!!}

  module _ {Ο : Signature} where
    instance
      IdxSet:IdxTerm : {A : K -> π°β} -> {{_ : IIdxSet K A}} -> IIdxSet K (Term Ο A)
      IdxSet:IdxTerm {A} {{_}} = of IdxTerm Ο ` A `

  -- instance
  --   IdxSet:IdxTermβ : {A : K -> π°β} -> {{_ : IIdxSet K A}} -> IIdxSet K (β A)
  --   IdxSet:IdxTermβ {A} = of _+-IdxSet_ π ` A `
  -- = #openstruct IdxTerm


  module _ {Ο : Signature} {V W : K -> π°β} where
    map-Term : {k : K} -> (β{k} -> V k -> W k) -> Term Ο V k -> Term Ο W k
    map-Termα΅₯ : {k : K} -> (β{k} -> V k -> W k) -> Termα΅₯ Ο V k -> Termα΅₯ Ο W k
    map-Terms : {ks : Vec K n} -> (β{k} -> V k -> W k) -> Terms Ο V ks -> Terms Ο W ks
    map-Termsα΅₯ : {ks : Vec K n} -> (β{k} -> V k -> W k) -> Termsα΅₯ Ο V ks -> Termsα΅₯ Ο W ks

    map-Termα΅₯ f (te s ts) = te s (map-Termsα΅₯ f ts)
    map-Termα΅₯ f (var x) = var (f x)

    map-Terms f [] = []
    map-Terms f (t β· ts) = map-Term f t β· map-Terms f ts

    map-Termsα΅₯ f (t β· ts) = map-Termα΅₯ f t β· map-Terms f ts
    map-Termsα΅₯ f (failβ· ts) = failβ· map-Termsα΅₯ f ts

    map-Term f (te s ts) = te s (map-Termsα΅₯ f ts)
    map-Term f (var x) = var (f x)
    map-Term f fail = fail


    commutes:mapβ£forget-Term : β{k} -> (f : β{k} -> V k -> W k) -> (t : Termα΅₯ Ο V k) -> map-Term f (forget-Term t) β‘ (forget-Term (map-Termα΅₯ f t))
    commutes:mapβ£forget-Term f (te s ts) = refl
    commutes:mapβ£forget-Term f (var x) = refl

    commutes:mapβ£forget-Terms : {ks : Vec K n} -> (f : β{k} -> V k -> W k) -> (ts : Termsα΅₯ Ο V ks) -> map-Terms f (forget-Terms ts) β‘ (forget-Terms (map-Termsα΅₯ f ts))
    commutes:mapβ£forget-Terms f (x β· ts) i = commutes:mapβ£forget-Term f x i β· map-Terms f ts
    commutes:mapβ£forget-Terms f (failβ· ts) i = fail β· commutes:mapβ£forget-Terms f ts i

    mapβ-Terms : {ks : Vec K n} -> (f : β{k} -> V k -> W k) -> β{k} -> {t : Term Ο V k} {ts : Terms Ο V ks} -> t β-Terms ts -> map-Term f t β-Terms map-Terms f ts
    mapβ-Terms f {k} {t} {.(t β· _)} this = this
    mapβ-Terms f {k} {t} {.(tβ β· _)} (tβ β· P) = _ β· mapβ-Terms f P

    mapIsFail-Terms : {ks : Vec K n} -> (f : β{k} -> V k -> W k) -> {ts : Terms Ο V ks} -> isFail-Terms ts -> isFail-Terms (map-Terms f ts)
    mapIsFail-Terms f [] = []
    mapIsFail-Terms f (fail β· P) = fail β· mapIsFail-Terms f P

    mapβ»ΒΉ-IsFail-Term : β{k} -> (f : β{k} -> V k -> W k) -> {t : Term Ο V k} -> isFail-Term (map-Term f t) -> isFail-Term t
    mapβ»ΒΉ-IsFail-Term f {t = fail} P = fail

    mapβ»ΒΉ-IsFail-Terms : {ks : Vec K n} -> (f : β{k} -> V k -> W k) -> {ts : Terms Ο V ks} -> isFail-Terms (map-Terms f ts) -> isFail-Terms ts
    mapβ»ΒΉ-IsFail-Terms f {ts = []} P = []
    mapβ»ΒΉ-IsFail-Terms f {ts = t β· ts} (x β· P) = mapβ»ΒΉ-IsFail-Term f x β· mapβ»ΒΉ-IsFail-Terms f P


  module _ {Ο : Signature} {V : K -> π°β} where

    functoriality-id:map-Term : {k : K} -> (t : Term Ο V k) -> map-Term id t β‘ t
    functoriality-id:map-Termα΅₯ : {k : K} -> (t : Termα΅₯ Ο V k) -> map-Termα΅₯ id t β‘ t
    functoriality-id:map-Termsα΅₯ : {ks : Vec K n} -> (ts : Termsα΅₯ Ο V ks) -> map-Termsα΅₯ id ts β‘ ts

    functoriality-id:map-Termα΅₯ (te s ts) i = te s (functoriality-id:map-Termsα΅₯ ts i)
    functoriality-id:map-Termα΅₯ (var x) = refl

    functoriality-id:map-Terms : {ks : Vec K n} -> (ts : Terms Ο V ks) -> map-Terms id ts β‘ ts
    functoriality-id:map-Terms [] = refl
    functoriality-id:map-Terms (t β· ts) i = functoriality-id:map-Term t i β· functoriality-id:map-Terms ts i

    functoriality-id:map-Termsα΅₯ (x β· ts) i = functoriality-id:map-Termα΅₯ x i β· functoriality-id:map-Terms ts i
    functoriality-id:map-Termsα΅₯ (failβ· ts) i = failβ· (functoriality-id:map-Termsα΅₯ ts i)

    functoriality-id:map-Term (te s ts) i = te s (functoriality-id:map-Termsα΅₯ ts i)
    functoriality-id:map-Term (var x) = refl
    functoriality-id:map-Term fail = refl


    ------

  module _ {Ο : Signature} {U V W : K -> π°β} where
    functoriality-β:map-Term   : (g : β{k} -> U k -> V k) (f : β{k} -> V k -> W k) {k : K} -> (t : Term Ο U k)            -> map-Term f (map-Term g t)    β‘ map-Term (g β f) t
    functoriality-β:map-Termα΅₯  : (g : β{k} -> U k -> V k) (f : β{k} -> V k -> W k) {k : K} -> (t : Termα΅₯ Ο U k)           -> map-Termα΅₯ f (map-Termα΅₯ g t)   β‘ map-Termα΅₯ (g β f) t
    functoriality-β:map-Terms  : (g : β{k} -> U k -> V k) (f : β{k} -> V k -> W k) {ks : Vec K n} -> (ts : Terms Ο U ks)  -> map-Terms f (map-Terms g ts)  β‘ map-Terms (g β f) ts
    functoriality-β:map-Termsα΅₯ : (g : β{k} -> U k -> V k) (f : β{k} -> V k -> W k) {ks : Vec K n} -> (ts : Termsα΅₯ Ο U ks) -> map-Termsα΅₯ f (map-Termsα΅₯ g ts) β‘ map-Termsα΅₯ (g β f) ts

    functoriality-β:map-Termα΅₯ g f (te s ts) i = te s (functoriality-β:map-Termsα΅₯ g f ts i)
    functoriality-β:map-Termα΅₯ g f (var x) = refl

    functoriality-β:map-Terms g f [] = refl
    functoriality-β:map-Terms g f (t β· ts) i = functoriality-β:map-Term g f t i β· functoriality-β:map-Terms g f ts i

    functoriality-β:map-Termsα΅₯ g f (x β· ts) i = functoriality-β:map-Termα΅₯ g f x i β· functoriality-β:map-Terms g f ts i
    functoriality-β:map-Termsα΅₯ g f (failβ· ts) i = failβ· (functoriality-β:map-Termsα΅₯ g f ts i)

    functoriality-β:map-Term g f (te s ts) i = te s (functoriality-β:map-Termsα΅₯ g f ts i)
    functoriality-β:map-Term g f (var x) = refl
    functoriality-β:map-Term g f fail = refl

  module _ {Ο : Signature} {V W : K -> π°β} where
    natural:join-te : (f : β{k} -> V k -> W k) {ks : Vec K (suc n)} -> β{k} -> (s : Ο k ks) -> (ts : Terms Ο V ks) -> map-Term f (join-te s ts) β‘ join-te s (map-Terms f ts)
    natural:join-te f s ts with split-+-Str (reduce-Terms ts) | split-+-Str (reduce-Terms (map-Terms f ts))
    ... | left x | left xβ = refl
    ... | left (x , xP) | just ((y , yP) , yQ) =
      let x1 : isFail-Terms (map-Terms f ts)
          x1 = mapIsFail-Terms f x
      in π-rec (leftβ’right (` reduce-isFail-Terms x1 .snd β»ΒΉ β yQ `))
    ... | just ((x , xP) , xQ) | left (y , yP) =
      let y1 = mapβ»ΒΉ-IsFail-Terms f y
      in π-rec (leftβ’right (` reduce-isFail-Terms y1 .snd β»ΒΉ β xQ `))
    ... | just ((x , xP) , xQ) | just ((y , yP) , yQ) with β‘ββ‘-Str xP
    ... | refl-StrId =
      let Q1 = forget-Terms y β‘β¨ yP β©
               map-Terms f (forget-Terms x) β‘β¨ commutes:mapβ£forget-Terms f x β©
               forget-Terms (map-Termsα΅₯ f x) β
          Q2 = isInjective:forget-Terms (β‘ββ‘-Str Q1)
      in Ξ» i -> te s (β‘-Strββ‘ Q2 (~ i))

    naturality:join-Term : (f : β{k} -> V k -> W k) {k : K} -> (t : Term Ο (Term Ο V) k) -> map-Term f (join-Term t) β‘ join-Term (map-Term (map-Term f) t)
    naturality:join-Termsα΅₯ : (f : β{k} -> V k -> W k) {ks : Vec K (suc n)} -> β{k} -> (s : Ο k ks) -> (ts : Termsα΅₯ Ο (Term Ο V) ks) -> map-Term f (join-te s (join-Termsα΅₯ ts)) β‘ join-te s (join-Termsα΅₯ (map-Termsα΅₯ (map-Term f) ts))

    naturality:join-Termα΅₯ : (f : β{k} -> V k -> W k) {k : K} -> (t : Termα΅₯ Ο (Term Ο V) k) -> map-Term f (join-Termα΅₯ t) β‘ join-Termα΅₯ (map-Termα΅₯ (map-Term f) t)
    naturality:join-Termα΅₯ f (te s ts) = naturality:join-Termsα΅₯ f s ts
    naturality:join-Termα΅₯ f (var x) = refl

    naturality:join-Terms : (f : β{k} -> V k -> W k) {ks : Vec K (n)} -> (ts : Terms Ο (Term Ο V) ks) -> map-Terms f (join-Terms ts) β‘ join-Terms (map-Terms (map-Term f) ts)
    naturality:join-Terms f [] = refl
    naturality:join-Terms f (t β· ts) i = naturality:join-Term f t i β· naturality:join-Terms f ts i

    naturality:join-Termsα΅₯2 : (f : β{k} -> V k -> W k) {ks : Vec K (n)} -> (ts : Termsα΅₯ Ο (Term Ο V) ks) -> map-Terms f (join-Termsα΅₯ ts) β‘ join-Termsα΅₯ (map-Termsα΅₯ (map-Term f) ts)
    naturality:join-Termsα΅₯2 f (x β· ts) i = naturality:join-Termα΅₯ f x i β· naturality:join-Terms f ts i
    naturality:join-Termsα΅₯2 f (failβ· ts) i = fail β· naturality:join-Termsα΅₯2 f ts i

    naturality:join-Termsα΅₯ f s ts = map-Term f (join-te s (join-Termsα΅₯ ts)) β‘β¨ natural:join-te f s (join-Termsα΅₯ ts) β©
                                    join-te s (map-Terms f (join-Termsα΅₯ ts)) β‘[ i ]β¨ join-te s (naturality:join-Termsα΅₯2 f ts i) β©
                                    join-te s (join-Termsα΅₯ (map-Termsα΅₯ (map-Term f) ts)) β


-- with split-+-Str (reduce-Terms (join-Termsα΅₯ ts)) | split-+-Str (reduce-Terms (join-Termsα΅₯ (map-Termsα΅₯ (map-Term f) ts)))
--     ... | left x | left xβ = refl
--     ... | left x | just xβ = {!!}
--     ... | just x | left xβ = {!!}
--     ... | just ((x , xP) , xQ) | just xβ = {!!}


    naturality:join-Term f (te s ts) = naturality:join-Termsα΅₯ f s ts
    naturality:join-Term f (var t) = refl
    naturality:join-Term f fail = refl

module _ {K : π°β} where
  module _ {Ο : Signature} {V : K -> π°β} where

    reduce-forget-Term : β{k} -> (t : Termα΅₯ Ο V k) -> β Ξ» x -> reduce-Term (forget-Term t) β‘-Str right x
    reduce-forget-Term (te s ts) = _ , refl
    reduce-forget-Term (var x) = _ , refl

    Β¬isFail-forget-Term : β{k} -> (t : Termα΅₯ Ο V k) -> isFail-Term (forget-Term t) -> π-π°
    Β¬isFail-forget-Term (te s ts) ()
    Β¬isFail-forget-Term (var x) ()

    Β¬isFail-forget-Terms : β{ks : Vec K n} -> (ts : Termsα΅₯ Ο V ks) -> isFail-Terms (forget-Terms ts) -> π-π°
    Β¬isFail-forget-Terms (x β· ts) (xP β· P) = Β¬isFail-forget-Term x xP
    Β¬isFail-forget-Terms (failβ· ts) (_ β· P) = Β¬isFail-forget-Terms ts P

    reduce-forget-Terms : β{ks : Vec K n} -> (ts : Termsα΅₯ Ο V ks) -> β Ξ» x -> reduce-Terms (forget-Terms ts) β‘-Str right x
    reduce-forget-Terms (x β· ts) with reduce-Term (forget-Term x) | reduce-forget-Term x
    ... | just xβ | Y = _ , refl
    reduce-forget-Terms (failβ·_ {k = k} ts) with reduce-Terms (forget-Terms ts)
    ... | left x = π-rec (Β¬isFail-forget-Terms _ x)
    ... | just x = _ , refl

    join-te-forget : β{ks : Vec K (suc n)} -> β{k} -> (s : Ο k ks)-> (ts : Termsα΅₯ Ο V ks) -> join-te s (forget-Terms ts) β‘ te s ts
    join-te-forget s ts with split-+-Str (reduce-Terms (forget-Terms ts))
    ... | left (x , xQ) = π-rec (Β¬isFail-forget-Terms _ x)
    ... | just ((x , xP) , xQ) with isInjective:forget-Terms (β‘ββ‘-Str xP)
    ... | refl-StrId = refl

    unit-r-join-Term : β{k} -> (x : Term Ο V k) -> join-Term (map-Term var x) β‘ x
    unit-r-join-Terms : β{ks : Vec K n} -> (ts : Terms Ο V ks) -> join-Terms (map-Terms var ts) β‘ ts
    unit-r-join-Termα΅₯ : β{k} -> (x : Termα΅₯ Ο V k) -> join-Termα΅₯ (map-Termα΅₯ var x) β‘ forget-Term x

    unit-r-join-Termsα΅₯ : β{ks : Vec K n} -> (ts : Termsα΅₯ Ο V ks) -> join-Termsα΅₯ (map-Termsα΅₯ var ts) β‘ forget-Terms ts
    unit-r-join-Termsα΅₯ (x β· ts) i = unit-r-join-Termα΅₯ x i β· unit-r-join-Terms ts i
    unit-r-join-Termsα΅₯ (failβ· ts) i = fail β· unit-r-join-Termsα΅₯ ts i

    unit-r-join-Terms [] = refl
    unit-r-join-Terms (t β· ts) i = unit-r-join-Term t i β· unit-r-join-Terms ts i

    unit-r-join-Termα΅₯ (te s ts) = join-te s (join-Termsα΅₯ (map-Termsα΅₯ var ts)) β‘[ i ]β¨ join-te s (unit-r-join-Termsα΅₯ ts i) β©
                                  join-te s (forget-Terms ts)                 β‘β¨ join-te-forget s ts β©
                                  te s ts                                     β
    unit-r-join-Termα΅₯ (var x) = refl

    unit-r-join-Term (te s ts) = join-te s (join-Termsα΅₯ (map-Termsα΅₯ var ts)) β‘[ i ]β¨ join-te s (unit-r-join-Termsα΅₯ ts i) β©
                                  join-te s (forget-Terms ts)                 β‘β¨ join-te-forget s ts β©
                                  te s ts                                     β
    unit-r-join-Term (var x) = refl
    unit-r-join-Term fail = refl


  private
    π : Category _
    π = Category:IdxSet K ββ

  module _ (Ο : Signature) where
    Functor:Term : Functor π π
    β¨ Functor:Term β© X = IdxTerm Ο X
    -- β¨ β¨ Functor:Term β© X β© = Term Ο β¨ X β©
    -- IIdxSet.ISet:this (of β¨ Functor:Term β© z) = {!!}
    β¨ IFunctor.map (of Functor:Term) f β© = map-Term β¨ f β©
    IFunctor.functoriality-id (of Functor:Term) = functoriality-id:map-Term
    IFunctor.functoriality-β (of Functor:Term) x = functoriality-β:map-Term _ _ x β»ΒΉ
    IFunctor.functoriality-β£ (of Functor:Term) p x i = map-Term (funExt p i) x

    Monad:Term : Monad π
    β¨ Monad:Term β© = Functor:Term
    β¨ IMonad.return (of Monad:Term) β© x = (var x)
    β¨ IMonad.join (of Monad:Term) β© = join-Term
    INatural.naturality (IMonad.INatural:return (of Monad:Term)) f x = refl
    INatural.naturality (IMonad.INatural:join (of Monad:Term)) f x = naturality:join-Term β¨ f β© x
    IMonad.unit-l-join (of Monad:Term) x = refl
    IMonad.unit-r-join (of Monad:Term) x = unit-r-join-Term x
    IMonad.assoc-join (of Monad:Term) = {!!}

{-

    Functor:TermZ2 = Functor:EitherT π (Monad:Term)
    Monad:TermZ2 = Monad:EitherT π (Monad:Term)

    TermZ2 : (V : K -> π°β) -> K -> π°β
    TermZ2 V k = Term Ο (β V) k

    IdxTermZ2 : (V : IdxSet K ββ) -> IdxSet K ββ
    IdxTermZ2 V = IdxTerm Ο (π + V)

    TermsZ2 : (V : K -> π°β) -> (Vec K n) -> π°β
    TermsZ2 V ks = Terms Ο (β V) ks

  module _ {Ο : Signature} {V W : IdxSet K ββ} where
    map-TermZ2 : {k : K} -> (V βΆ W) -> TermZ2 Ο β¨ V β© k -> TermZ2 Ο β¨ W β© k
    map-TermZ2 {k} f = β¨ map {{of Functor:TermZ2 Ο}} f β© {k}

    map-TermsZ2 : {ks : Vec K n} -> (V βΆ W) -> TermsZ2 Ο β¨ V β© ks -> TermsZ2 Ο β¨ W β© ks
    map-TermsZ2 f = map-Terms (β¨ map-+-r {c = π} f β© {_})

  module _ {Ο : Signature} {V : IdxSet K ββ} where
    join-TermZ2 : {k : K} -> TermZ2 Ο (TermZ2 Ο β¨ V β©) k -> TermZ2 Ο β¨ V β© k
    join-TermZ2 {k} x = β¨ join {{of Monad:TermZ2 Ο}} {A = V} β© {k} x
-}
