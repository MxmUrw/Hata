

module Verification.Core.Theory.Example.Type.HM.Definition where

open import Verification.Conventions hiding (_,_)
-- open import Verification.Unification.Instance.SignatureZ3
open import Verification.Core.Theory.Presentation.Signature.Definition



data Type (A : π°β) :  π°β where
  _β_ : Type A -> Type A -> Type A
  π΅ : Type A
  π : Type A
  var : A -> Type A

data Ctx (B A : π°β) : π°β where
  [] : Ctx B A
  _,_ : Ctx B A -> Type B -> Ctx B A
  var : A -> Ctx B A

infixl 50 _,_
infixr 70 _β_

data Jdgm (B A : π°β) : π°β where
  _β’_ : Ctx B A -> Type B -> Jdgm B A

-- data _β’_ : Ctx -> Type -> π°β where
--   judge : Ctx

data K : π°β where
  kT kC kJ : K
-- K = π-π°

V : β -> β -> K -> π°β
V nT nC kT = Fin-R nT
V nT nC kC = Fin-R nC
V nT nC kJ = π-π°

data Ο : K -> Vec K n -> π°β where
  `β` : Ο kT (kT β· kT β· [])
  `π΅` : Ο kT []
  `π` : Ο kT []
  `[]` : Ο kC []
  `,`  : Ο kC (kC β· kT β· [])
  `β’`  : Ο kJ (kC β· kT β· [])

ΟT : Term Ο (V m n) kT -> Type (Fin-R m)
ΟT (te `β` (x β· (y β· []))) = ΟT x β ΟT y
ΟT (te `π΅` []) = π΅
ΟT (te `π` []) = π
ΟT (var x) = var x

ΟC : Term Ο (V m n) kC -> Ctx (Fin-R m) (Fin-R n)
ΟC (te `[]` []) = []
ΟC (te `,` (x β· (y β· []))) = ΟC x , ΟT y
ΟC (var x) = var x

ΟJ : Term Ο (V m n) kJ -> Jdgm (Fin-R m) (Fin-R n)
ΟJ (te `β’` (x β· (y β· []))) = ΟC x β’ ΟT y

ΟT : Type (Fin-R m) -> Term Ο (V m n) kT
ΟT (t β s) = te `β` (ΟT t β· ΟT s β· [])
ΟT π΅ = te `π΅` []
ΟT π = te `π` []
ΟT (var x) = var x

ΟC : Ctx (Fin-R m) (Fin-R n) -> Term Ο (V m n) kC
ΟC [] = te `[]` []
ΟC (t , x) = te `,` (ΟC t β· ΟT x β· [])
ΟC (var x) = var x

ΟJ : Jdgm (Fin-R m) (Fin-R n) -> Term Ο (V m n) kJ
ΟJ (x β’ y) = te `β’` (ΟC x β· ΟT y β· [])


data Rule {K} (Ο : Signature K) (V : K -> π°β) (k : K) : π°β where
  _β©_ : Vec (Term Ο V k) n -> Term Ο V k -> Rule Ο V k

RuleΞ : β -> β -> π°β
RuleΞ m n = Rule Ο (V m n) kJ

pattern Ξ = var zero
pattern Ξ± = var zero
pattern Ξ² = var (suc zero)

var0-Ξ : RuleΞ 1 1
var0-Ξ = [] β© ΟJ ((Ξ , Ξ±) β’ Ξ±)

varSuc-Ξ : RuleΞ 2 1
varSuc-Ξ = (ΟJ (Ξ β’ Ξ±) β· []) β© ΟJ (Ξ , Ξ² β’ Ξ±)

lambda-Ξ : RuleΞ 2 1
lambda-Ξ = (ΟJ (Ξ , Ξ± β’ Ξ²) β· []) β© ΟJ (Ξ β’ Ξ± β Ξ²)

app-Ξ : RuleΞ 2 1
app-Ξ = (ΟJ (Ξ β’ Ξ± β Ξ²) β· ΟJ (Ξ β’ Ξ±) β· []) β© ΟJ (Ξ β’ Ξ²)









