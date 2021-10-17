
module Verification.Unification.Instance.HMType where

open import Verification.Conventions hiding (_,_)
-- open import Verification.Unification.Instance.SignatureZ3
open import Verification.Core.Syntax.Signature



data Type (A : 𝒰₀) :  𝒰₀ where
  _⇒_ : Type A -> Type A -> Type A
  𝐵 : Type A
  𝑁 : Type A
  var : A -> Type A

data Ctx (B A : 𝒰₀) : 𝒰₀ where
  [] : Ctx B A
  _,_ : Ctx B A -> Type B -> Ctx B A
  var : A -> Ctx B A

infixl 50 _,_
infixr 70 _⇒_

data Jdgm (B A : 𝒰₀) : 𝒰₀ where
  _⊢_ : Ctx B A -> Type B -> Jdgm B A

-- data _⊢_ : Ctx -> Type -> 𝒰₀ where
--   judge : Ctx

data K : 𝒰₀ where
  kT kC kJ : K
-- K = 𝟙-𝒰

V : ℕ -> ℕ -> K -> 𝒰₀
V nT nC kT = Fin-R nT
V nT nC kC = Fin-R nC
V nT nC kJ = 𝟘-𝒰

data σ : K -> Vec K n -> 𝒰₀ where
  `⇒` : σ kT (kT ∷ kT ∷ [])
  `𝐵` : σ kT []
  `𝑁` : σ kT []
  `[]` : σ kC []
  `,`  : σ kC (kC ∷ kT ∷ [])
  `⊢`  : σ kJ (kC ∷ kT ∷ [])

ϕT : Term σ (V m n) kT -> Type (Fin-R m)
ϕT (te `⇒` (x ∷ (y ∷ []))) = ϕT x ⇒ ϕT y
ϕT (te `𝐵` []) = 𝐵
ϕT (te `𝑁` []) = 𝑁
ϕT (var x) = var x

ϕC : Term σ (V m n) kC -> Ctx (Fin-R m) (Fin-R n)
ϕC (te `[]` []) = []
ϕC (te `,` (x ∷ (y ∷ []))) = ϕC x , ϕT y
ϕC (var x) = var x

ϕJ : Term σ (V m n) kJ -> Jdgm (Fin-R m) (Fin-R n)
ϕJ (te `⊢` (x ∷ (y ∷ []))) = ϕC x ⊢ ϕT y

ψT : Type (Fin-R m) -> Term σ (V m n) kT
ψT (t ⇒ s) = te `⇒` (ψT t ∷ ψT s ∷ [])
ψT 𝐵 = te `𝐵` []
ψT 𝑁 = te `𝑁` []
ψT (var x) = var x

ψC : Ctx (Fin-R m) (Fin-R n) -> Term σ (V m n) kC
ψC [] = te `[]` []
ψC (t , x) = te `,` (ψC t ∷ ψT x ∷ [])
ψC (var x) = var x

ψJ : Jdgm (Fin-R m) (Fin-R n) -> Term σ (V m n) kJ
ψJ (x ⊢ y) = te `⊢` (ψC x ∷ ψT y ∷ [])


data Rule {K} (σ : Signature {K = K}) (V : K -> 𝒰₀) (k : K) : 𝒰₀ where
  _⊩_ : Vec (Term σ V k) n -> Term σ V k -> Rule σ V k

RuleΛ : ℕ -> ℕ -> 𝒰₀
RuleΛ m n = Rule σ (V m n) kJ

pattern Γ = var zero
pattern α = var zero
pattern β = var (suc zero)

var0-Λ : RuleΛ 1 1
var0-Λ = [] ⊩ ψJ ((Γ , α) ⊢ α)

varSuc-Λ : RuleΛ 2 1
varSuc-Λ = (ψJ (Γ ⊢ α) ∷ []) ⊩ ψJ (Γ , β ⊢ α)

lambda-Λ : RuleΛ 2 1
lambda-Λ = (ψJ (Γ , α ⊢ β) ∷ []) ⊩ ψJ (Γ ⊢ α ⇒ β)

app-Λ : RuleΛ 2 1
app-Λ = (ψJ (Γ ⊢ α ⇒ β) ∷ ψJ (Γ ⊢ α) ∷ []) ⊩ ψJ (Γ ⊢ β)














