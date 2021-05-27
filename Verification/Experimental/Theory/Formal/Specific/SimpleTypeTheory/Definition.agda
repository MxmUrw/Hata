
module Verification.Experimental.Theory.Formal.Specific.SimpleTypeTheory.Definition where

open import Verification.Experimental.Conventions
open import Verification.Experimental.Set.Setoid.Definition
open import Verification.Experimental.Set.Discrete
open import Verification.Experimental.Data.Universe.Everything
open import Verification.Experimental.Data.Prop.Everything
open import Verification.Experimental.Order.WellFounded.Definition
open import Verification.Experimental.Order.Preorder
open import Verification.Experimental.Category.Std.Category.Definition
-- open import Verification.Experimental.Category.Std.Limit.Specific.Coequalizer
-- open import Verification.Experimental.Category.Std.Category.As.Monoid
-- open import Verification.Experimental.Algebra.MonoidWithZero.Definition
-- open import Verification.Experimental.Algebra.MonoidWithZero.Ideal
open import Verification.Experimental.Theory.Computation.Problem.Definition


--------------------------------------------------------------------
-- some basic types in order to not import from any library



-- cong-Str : ∀ {A : 𝒰 ℓ} {B : 𝒰 ℓ'} -> (f : A -> B) -> ∀{a a'} -> (a ≣ a') -> (f a ≣ f a')
-- cong-Str f refl-StrId = refl-StrId

cong2 : ∀ {A B C : 𝒰 ℓ} -> (f : A -> B -> C) -> ∀{a b a' b'} -> (a ≣ a') -> (b ≣ b') -> (f a b ≣ f a' b')
cong2 f refl-StrId refl-StrId = refl-StrId

cong3 : ∀ {A B C D : 𝒰 ℓ} -> (f : A -> B -> C -> D) -> ∀{a b c a' b' c'} -> (a ≣ a') -> (b ≣ b') -> (c ≣ c') -> (f a b c ≣ f a' b' c')
cong3 f refl-StrId refl-StrId refl-StrId = refl-StrId

-- sym : ∀{A : 𝒰 ℓ} -> {a b : A} -> (a ≣ b) -> b ≣ a
-- sym refl-StrId = refl-StrId

-- transport-Str : ∀{A B : 𝒰 ℓ} -> (p : A ≣ B) -> A -> B
-- transport-Str refl-StrId a = a



--------------------------------------------------------------------
--------------------------------------------------------------------
-- Beginning of actual code

-- Base types: natural numbers and booleans
data BaseType : 𝒰₀ where
  NN : BaseType
  BB : BaseType

-- compound types, no product types at the moment
data Type : 𝒰₀ where
  Base : BaseType -> Type
  _⇒_ : (A : Type) -> (B : Type) -> Type
  -- _×-𝒰'_ : (A B : Type) -> Type

infixr 50 _⇒_


-- Defining contexts
--
-- Since the goal is to allow typechecking of a collection of statements/definitions,
-- we have two kinds of contexts:
-- 1: A context Γ of type FCtx, which contains the typing information for free variables in the current term.
-- 2: A context Δ of type BCtx, which contains the typing info and terms of previously typechecked statements.
--    (Thus it has to be defined mutually together with the typed terms.)


data RList (A : 𝒰₀) : 𝒰₀ where
  [] : RList A
  _,,_ : RList A -> A -> RList A


FCtx = RList (Type)

data BCtx : 𝒰₀
data _∣_⊢_ : BCtx -> FCtx -> Type -> 𝒰₀


data BCtx  where
  [] : BCtx
  _,,_ : ∀{A} -> (Δ : BCtx) -> (t : Δ ∣ [] ⊢ A) -> BCtx

infixl 70 _,,_


-- The definition of intrinsically typed terms
--
-- Beginning with _∣πF_ and _∣πB_ for projecting variables out of FCtx's and BCtx's, respectively

data _∣πF_ : FCtx -> (Type) -> 𝒰₀ where
  zero : {Γ : FCtx} -> {A : Type} -> (Γ ,, A) ∣πF A
  suc : {Γ : FCtx} -> {A B : Type} -> Γ ∣πF A -> (Γ ,, B) ∣πF A

data _∣πB_ : BCtx -> Type -> 𝒰₀ where
  zero : {A : Type} -> {Δ : BCtx} -> {t : Δ ∣ [] ⊢ A} -> (Δ ,, t) ∣πB (A)
  suc : ∀{A B} -> {Δ : BCtx} -> {s : Δ ∣ [] ⊢ B } -> Δ ∣πB A -> (Δ ,, s) ∣πB A

-- We do not allow lambda expressions in the first argument of an application.
-- Even though this is potentially too restricting, for the moment we only allow FVars and BVars here.
data _∣_⊢APP_ : BCtx -> FCtx -> Type -> 𝒰₀ where
  app : {A : Type} {B : Type} -> {Δ : BCtx} -> {Γ : FCtx} -> Δ ∣ Γ ⊢APP A ⇒ B -> Δ ∣ Γ ⊢ A -> Δ ∣ Γ ⊢APP B
  fvar : ∀{A}   -> {Δ : BCtx} -> {Γ : FCtx} -> Γ ∣πF (A) -> Δ ∣ Γ ⊢APP A
  bvar : ∀{A}   -> {Δ : BCtx} -> {Γ : FCtx} -> Δ ∣πB (A) -> Δ ∣ Γ ⊢APP A

-- The actual typed terms
data _∣_⊢_ where
  tB   :           ∀{Δ Γ} -> Bool -> Δ ∣ Γ ⊢ Base BB
  tif_then_else : ∀{Δ Γ A} -> (t : Δ ∣ Γ ⊢ Base BB) -> (a : Δ ∣ Γ ⊢ A) -> (b : Δ ∣ Γ ⊢ A) -> Δ ∣ Γ ⊢ A
  t0   :           ∀{Δ Γ} -> Δ ∣ Γ ⊢ Base NN
  tS   :           ∀{Δ Γ} -> Δ ∣ Γ ⊢ Base NN -> Δ ∣ Γ ⊢ Base NN
  tNrec : ∀{Γ Δ A} -> (n : Δ ∣ Γ ⊢ Base NN) -> (t0 : Δ ∣ Γ ⊢ A) -> (ts : Δ ∣ Γ ⊢ A ⇒ A) -> Δ ∣ Γ ⊢ A
  fvar : ∀{A Δ Γ} -> Γ ∣πF A -> Δ ∣ Γ ⊢ A
  bvar : ∀{A Δ Γ} -> Δ ∣πB A -> Δ ∣ Γ ⊢ A
  APP : ∀{A Δ Γ} -> Δ ∣ Γ ⊢APP A -> Δ ∣ Γ ⊢ A
  Λ    : ∀{Δ Γ} {A : Type} {B : Type} -> (Δ ∣ (Γ ,, (A)) ⊢ B) -> Δ ∣ Γ ⊢ A ⇒ B



---------------------------------------------------------------------------
-- The evaluator
--
-- It evaluates directly into agda values.

evalT : Type -> 𝒰₀
evalT (Base NN) = ℕ
evalT (Base BB) = Bool
evalT (A ⇒ B) = evalT A -> evalT B

execTimes : ∀{A : 𝒰 ℓ} -> ℕ -> (A -> A) -> A -> A
execTimes zero f a = a
execTimes (suc n) f a = f (execTimes n f a)


-- Environment, containing already all known values for types in a ctx Γ
Env : FCtx -> 𝒰₀
Env [] = ⊤-𝒰
Env (G ,, A) = Env G ×-𝒰 evalT A


-- The actual evaluator
eval : ∀{Δ Γ A} -> Env Γ -> Δ ∣ Γ ⊢ A -> evalT A
evalAPP : ∀{Δ Γ A} -> Env Γ -> Δ ∣ Γ ⊢APP A -> evalT A

getFVar : ∀{Γ A} -> (E : Env Γ) -> (x : Γ ∣πF A) -> evalT A
getFVar (E , x) zero = x
getFVar (E , y) (suc x) = getFVar E x

getBVar : ∀{Δ A} -> (x : Δ ∣πB A) -> evalT A
getBVar {(D ,, A)} zero = eval tt A
getBVar {(D ,, A)} (suc x) = getBVar x

evalAPP E (app t x) = evalAPP E t (eval E x)
evalAPP E (fvar x) = getFVar E x
evalAPP E (bvar x) = getBVar x

eval E (tB x) = x
eval E (tif x then a else b) with eval E x
... | false = eval E a
... | true = eval E b
eval E t0 = 0
eval E (tS x) = suc (eval E x)
eval E (tNrec n f0 fs) = execTimes (eval E n) (eval E fs) (eval E f0)
eval E (fvar x) = getFVar E x
eval E (bvar x) = getBVar x
eval E (APP x) = evalAPP E x
eval E (Λ x) = λ a -> eval (E , a) x


---------------------------------------------------------------------------
-- Testing the evaluator
--
-- Addition and multiplication of natural numbers implemented in typed terms.

-- embedding a nat into the TT
reN : ∀{Δ Γ} -> ℕ -> Δ ∣ Γ ⊢ Base NN
reN zero = t0
reN (suc n) = tS (reN n)

add : [] ∣ [] ⊢ Base NN ⇒ Base NN ⇒ Base NN
add = Λ (Λ (tNrec (fvar (suc zero)) (fvar zero) (Λ (tS (fvar zero)))))

mult : [] ,, add ∣ [] ⊢ Base NN ⇒ Base NN ⇒ Base NN
mult = Λ (Λ (tNrec (fvar (suc zero)) (t0) (Λ (APP (app (app (bvar zero) (fvar zero)) (fvar (suc zero)))))))

-- calculating 7 * 18
v1 : ([] ,, add ,, mult) ∣ [] ⊢ Base NN
v1 = (APP (app (app (bvar zero) (reN 7)) (reN 18)))

-- the result of 7 * 18 is 126
test1 : eval tt v1 ≣ 126
test1 = refl-StrId






---------------------------------------------------------------------------
-- Definition of untyped terms
data TermAPP : 𝒰₀
data Term : 𝒰₀ where
  tB   :           Bool -> Term
  tif_then_else : (t : Term) -> (a : Term) -> (b : Term) -> Term
  t0   :           Term
  tS   :           Term -> Term
  tNrec : Term -> Term -> Term -> Term
  fvar : ℕ -> Term
  bvar : ℕ -> Term
  APP : TermAPP -> Term
  Λ    : Term -> Term

data TermAPP where
  app : TermAPP -> Term -> TermAPP
  fvar : ℕ -> TermAPP
  bvar : ℕ -> TermAPP


---------------------------------------------------------------------------
-- Relation between untyped terms (Term) and intrinsically typed ones (_∣_⊢_),
-- called 'terms typed by annotation'
-- we write Δ ∣ Γ ⊢ A / t, for what would usually be written as Δ ∣ Γ ⊢ t : A

data _∣_⊢_/_ : BCtx -> FCtx -> Type -> Term -> 𝒰₀

data _∣πF_/_ : FCtx -> (Type) -> ℕ -> 𝒰₀ where
  zero : {Γ : FCtx} -> {A : Type} -> (Γ ,, A) ∣πF A / zero
  suc : ∀{n} {Γ : FCtx} -> {A B : Type} -> Γ ∣πF A / n -> (Γ ,, B) ∣πF A / suc n

data _∣πB_/_ : BCtx -> Type -> ℕ -> 𝒰₀ where
  zero : {A : Type} -> {Δ : BCtx} -> {t : Δ ∣ [] ⊢ A} -> (Δ ,, t) ∣πB (A) / zero
  suc : ∀{A B n} -> {Δ : BCtx} -> {s : Δ ∣ [] ⊢ B} -> Δ ∣πB A / n -> (Δ ,, s) ∣πB A / suc n

data _∣_⊢APP_/_ : BCtx -> FCtx -> Type -> TermAPP -> 𝒰₀ where
  app : ∀{A B Δ Γ f x} -> Δ ∣ Γ ⊢APP A ⇒ B / f  -> Δ ∣ Γ ⊢ A / x -> Δ ∣ Γ ⊢APP B / app f x
  fvar : ∀{A Δ Γ n} -> Γ ∣πF (A) / n -> Δ ∣ Γ ⊢APP A / fvar n
  bvar : ∀{A Δ Γ n} -> Δ ∣πB (A) / n -> Δ ∣ Γ ⊢APP A / bvar n

data _∣_⊢_/_ where
  tB   :           ∀{Δ Γ} -> (x : Bool) -> Δ ∣ Γ ⊢ Base BB / tB x
  tif_then_else : ∀{Δ Γ A xx aa bb} -> (t : Δ ∣ Γ ⊢ Base BB / xx) -> (a : Δ ∣ Γ ⊢ A / aa) -> (b : Δ ∣ Γ ⊢ A / bb) -> Δ ∣ Γ ⊢ A / (tif xx then aa else bb)
  t0   :           ∀{Δ Γ} -> Δ ∣ Γ ⊢ Base NN / t0
  tS   :           ∀{Δ Γ n} -> Δ ∣ Γ ⊢ Base NN / n -> Δ ∣ Γ ⊢ Base NN / (tS n)
  tNrec : ∀{Γ Δ A tn tfs tf0} -> (n : Δ ∣ Γ ⊢ Base NN / tn) -> (f0 : Δ ∣ Γ ⊢ A / tf0) -> (fs : Δ ∣ Γ ⊢ A ⇒ A / tfs) -> Δ ∣ Γ ⊢ A / (tNrec tn tf0 tfs)
  fvar : ∀{A Δ Γ x} -> Γ ∣πF A / x -> Δ ∣ Γ ⊢ A / fvar x
  bvar : ∀{A Δ Γ x} -> Δ ∣πB A / x -> Δ ∣ Γ ⊢ A / bvar x
  APP : ∀{A Δ Γ a} -> Δ ∣ Γ ⊢APP A / a -> Δ ∣ Γ ⊢ A / APP a
  Λ    : ∀{Δ Γ A B t} -> (Δ ∣ (Γ ,, (A)) ⊢ B / t) -> Δ ∣ Γ ⊢ A ⇒ B / Λ t


--------------------------------------------------------------------
-- Functions for going from annotated terms (_∣_⊢_/_) to intrinsically typed terms (_∣_⊢_)
-- and from there to untyped terms (Term)

module AnnToTTermM where
  f : ∀{Δ Γ A t} -> Δ ∣ Γ ⊢ A / t -> Δ ∣ Γ ⊢ A

  fF : ∀{Γ A t} -> Γ ∣πF A / t -> Γ ∣πF A
  fF zero = zero
  fF (suc n) = suc (fF n)

  fB : ∀{Δ A t} -> Δ ∣πB A / t -> Δ ∣πB A
  fB zero = zero
  fB (suc n) = suc (fB n)

  fA : ∀{Δ Γ A t} -> Δ ∣ Γ ⊢APP A / t -> Δ ∣ Γ ⊢APP A
  fA (app x x₁) = app (fA x) (f x₁)
  fA (fvar x) = fvar (fF x)
  fA (bvar x) = bvar (fB x)

  f (tB x) = tB x
  f (tif s then a else b) = tif (f s) then (f a) else (f b)
  f t0 = t0
  f (tS s) = tS (f s)
  f (tNrec s a b) = tNrec (f s) (f a) (f b)
  f (fvar x) = fvar (fF x)
  f (bvar x) = bvar (fB x)
  f (APP x) = APP (fA x)
  f (Λ s) = Λ (f s)

AnnToTTerm = AnnToTTermM.f

module TTermToTermM where
  f : ∀{Δ Γ A} -> Δ ∣ Γ ⊢ A -> Term

  fF : ∀{Γ A} -> Γ ∣πF A -> ℕ
  fF zero = zero
  fF (suc n) = suc (fF n)

  fB : ∀{Δ A} -> Δ ∣πB A -> ℕ
  fB zero = zero
  fB (suc n) = suc (fB n)

  fA : ∀{Δ Γ A} -> Δ ∣ Γ ⊢APP A -> TermAPP
  fA (app x x₁) = app (fA x) (f x₁)
  fA (fvar x) = fvar (fF x)
  fA (bvar x) = bvar (fB x)

  f (tB x) = tB x
  f (tif s then a else b) = tif (f s) then (f a) else (f b)
  f t0 = t0
  f (tS s) = tS (f s)
  f (tNrec s a b) = tNrec (f s) (f a) (f b)
  f (fvar x) = fvar (fF x)
  f (bvar x) = bvar (fB x)
  f (APP x) = APP (fA x)
  f (Λ s) = Λ (f s)

TTermToTerm = TTermToTermM.f


--------------------------------------------------------------------
-- Proof that these are inverses of each other
roundTrip : ∀{Δ Γ A t} -> (x : Δ ∣ Γ ⊢ A / t) -> TTermToTerm (AnnToTTerm x) ≣ t

roundTripF : ∀{Γ A t} -> (x :  Γ ∣πF A / t) -> TTermToTermM.fF (AnnToTTermM.fF x) ≣ t
roundTripF zero = refl-StrId
roundTripF (suc x) = cong-Str suc (roundTripF x)

roundTripB : ∀{Δ A t} -> (x : Δ ∣πB A / t) -> TTermToTermM.fB (AnnToTTermM.fB x) ≣ t
roundTripB zero = refl-StrId
roundTripB (suc x) = cong-Str suc (roundTripB x)

roundTripAPP : ∀{Δ Γ A t} -> (x : Δ ∣ Γ ⊢APP A / t) -> TTermToTermM.fA (AnnToTTermM.fA x) ≣ t
roundTripAPP (app x y) = cong2 app (roundTripAPP x) (roundTrip y)
roundTripAPP (fvar x) = cong-Str fvar (roundTripF x)
roundTripAPP (bvar x) = cong-Str bvar (roundTripB x)


roundTrip (tB x) = refl-StrId
roundTrip (tif x then x₁ else x₂) with roundTrip x | roundTrip x₁ | roundTrip x₂
... | X | Y | Z = cong3 tif_then_else X Y Z
roundTrip t0 = refl-StrId
roundTrip (tS x) with roundTrip x
... | X = cong-Str tS X
roundTrip (tNrec x x₁ x₂) = cong3 tNrec (roundTrip x) (roundTrip x₁) (roundTrip x₂)
roundTrip (fvar x) = cong-Str fvar (roundTripF x)
roundTrip (bvar x) = cong-Str bvar (roundTripB x)
roundTrip (APP x) = cong-Str APP (roundTripAPP x)
roundTrip (Λ x) with roundTrip x
... | X = cong-Str Λ X



--------------------------------------------------------------------
-- Decidability of equality of types

decideBaseTypeEq : ∀(A B : BaseType) -> (A ≣ B -> 𝟘-𝒰) +-𝒰 (A ≣ B)
decideBaseTypeEq NN NN = right refl-StrId
decideBaseTypeEq NN BB = left (λ ())
decideBaseTypeEq BB NN = left (λ ())
decideBaseTypeEq BB BB = right refl-StrId

TypeToBase : Type -> BaseType
TypeToBase (Base a) = a
TypeToBase (a ⇒ b) = NN

decideTypeEq : ∀(A B : Type) -> (A ≣ B -> 𝟘-𝒰) +-𝒰 (A ≣ B)
decideTypeEq (Base x) (Base y) with decideBaseTypeEq x y
... | just yesp = just (cong-Str Base yesp)
... | left nop = left (λ p -> nop (cong-Str TypeToBase p))
decideTypeEq (Base x) (B ⇒ B₁) = left (λ ())
decideTypeEq (A ⇒ A₁) (Base x) = left (λ ())
decideTypeEq (A ⇒ A') (B ⇒ B') with decideTypeEq A B | decideTypeEq A' B'
... | just refl-StrId | just refl-StrId = right refl-StrId
... | left noA | _ = left (λ {refl-StrId -> noA refl-StrId})
... | _ | left noB = left (λ {refl-StrId -> noB refl-StrId})

decideBaseTypeEq-id : ∀ A -> decideBaseTypeEq A A ≣ right refl-StrId
decideBaseTypeEq-id NN = refl-StrId
decideBaseTypeEq-id BB = refl-StrId

decideTypeEq-id : ∀ A -> decideTypeEq A A ≣ right refl-StrId
decideTypeEq-id (Base x) with decideBaseTypeEq x x | decideBaseTypeEq-id x
... | .(just refl-StrId) | refl-StrId = refl-StrId
decideTypeEq-id (A ⇒ B) with decideTypeEq A A | decideTypeEq B B | decideTypeEq-id A | decideTypeEq-id B
... | .(just refl-StrId) | .(just refl-StrId) | refl-StrId | refl-StrId = refl-StrId


--------------------------------------------------------------------
-- uniqueness of typing for APP terms

Base=Arr-𝟘-𝒰 : ∀{A B C} -> Base A ≣ B ⇒ C -> 𝟘-𝒰
Base=Arr-𝟘-𝒰 ()

Arr-fst : Type -> Type
Arr-fst (Base x) = Base x
Arr-fst (A ⇒ A₁) = A

Arr-snd : Type -> Type
Arr-snd (Base x) = Base x
Arr-snd (A ⇒ B) = B


uniqueFVar : ∀{Γ A B t} -> Γ ∣πF A / t -> Γ ∣πF B / t -> A ≣ B
uniqueFVar zero zero = refl-StrId
uniqueFVar (suc x) (suc y) = uniqueFVar x y

uniqueBVar : ∀{Δ A B t} -> Δ ∣πB A / t -> Δ ∣πB B / t -> A ≣ B
uniqueBVar zero zero = refl-StrId
uniqueBVar (suc x) (suc y) = uniqueBVar x y

uniqueAPP : ∀{Δ Γ A B t} -> Δ ∣ Γ ⊢APP A / t -> Δ ∣ Γ ⊢APP B / t -> A ≣ B
uniqueAPP (app x x') (app y y') = cong-Str Arr-snd (uniqueAPP x y)
uniqueAPP (fvar x) (fvar y) = uniqueFVar x y
uniqueAPP (bvar x) (bvar y) = uniqueBVar x y

-- NOTE: uniqueness for types in general DOES NOT WORK, since because we are not using church, we are not, in fact unique



--------------------------------------------------------------------
-- The Typechecker
--
-- consisting of the 'check' and 'syn' function for type checking and type inference
-- (and their respective counterparts for APP, FVar, BVar)

check : ∀ (Δ : BCtx) (Γ : FCtx) (t : Term) (A : Type) -> (Δ ∣ Γ ⊢ A / t -> 𝟘-𝒰) +-𝒰 (Δ ∣ Γ ⊢ A / t)
syn : ∀ (Δ : BCtx) (Γ : FCtx) (t : TermAPP) -> ((∑ λ A -> Δ ∣ Γ ⊢APP A / t) -> 𝟘-𝒰) +-𝒰 (∑ λ A -> Δ ∣ Γ ⊢APP A / t)

synFVar : ∀ (Γ : FCtx) (n : ℕ) -> ((∑ λ A -> Γ ∣πF A / n) -> 𝟘-𝒰) +-𝒰 (∑ λ A -> Γ ∣πF A / n)
synFVar [] n = left (λ ())
synFVar (G ,, x) zero = right (x , zero)
synFVar (G ,, x) (suc n) with synFVar G n
... | just (A , p) = right (A , suc p)
... | left C = left (λ {(A , suc p) -> C (_ , p)})

synBVar : ∀ (Δ : BCtx) (n : ℕ) -> ((∑ λ A -> Δ ∣πB A / n) -> 𝟘-𝒰) +-𝒰 (∑ λ A -> Δ ∣πB A / n)
synBVar [] n = left (λ ())
synBVar (B ,, t) (zero) = right (_ , zero)
synBVar (B ,, t) (suc n) with synBVar B n
... | just (A , p) = right (_ , suc p)
... | left C = left (λ {(A , suc p) -> C (_ , p)})

syn Δ Γ (app t x) with syn Δ Γ t
... | left (C) = left (λ {(A , app nt nx) -> C (_ , nt)})
... | just (Base A , nt) = left (λ {(A , app nnt nnx) -> let CC = uniqueAPP nt nnt in Base=Arr-𝟘-𝒰 CC})
... | just (A ⇒ B , nt) with check Δ Γ x A
... | just xx = right (B , app nt xx)
... | left C = left (λ {(A2 , app nnt nnx) -> let CC = uniqueAPP nt nnt in C (transport-Str (cong-Str (λ α -> Δ ∣ Γ ⊢ Arr-fst α / x) (sym CC)) nnx)})
syn Δ Γ (fvar x) with synFVar Γ x
... | just (A , xx) = right (A , fvar xx)
... | left C = left (λ {(_ , fvar x) -> C (_ , x)})
syn Δ Γ (bvar x) with synBVar Δ x
... | just (A , xx) = right (A , bvar xx)
... | left C = left (λ {(_ , bvar x) -> C (_ , x)})


checkFVar : ∀ (Γ : FCtx) (A : Type) -> (t : ℕ) -> (Γ ∣πF A / t -> 𝟘-𝒰) +-𝒰 (Γ ∣πF A / t)
checkFVar Γ A t with synFVar Γ t
... | just (B , x) with decideTypeEq A B
... | just refl-StrId = right x
... | left C = left (λ xx -> C (uniqueFVar xx x))
checkFVar Γ A t | left C = left (λ x -> C (_ , x))

checkBVar : ∀ (Δ : BCtx)(A : Type) -> (t : ℕ) -> (Δ ∣πB A / t -> 𝟘-𝒰) +-𝒰 (Δ ∣πB A / t)
checkBVar Γ A t with synBVar Γ t
... | just (B , x) with decideTypeEq A B
... | just refl-StrId = right x
... | left C = left (λ xx -> C (uniqueBVar xx x))
checkBVar Γ A t | left C = left (λ x -> C (_ , x))


check Δ Γ (tB x) (Base NN) = left (λ ())
check Δ Γ (tB x) (Base BB) = right (tB x)
check Δ Γ (tB x) (A ⇒ A₁) = left (λ ())
check Δ Γ (tif t then a else b) A with check Δ Γ t (Base BB) | check Δ Γ a A | check Δ Γ b A
... | just x | just y | just z = right (tif x then y else z)
... | left x | y | z = left (λ {(tif xx then yy else zz) -> x xx})
... | x | left y | z = left (λ {(tif xx then yy else zz) -> y yy})
... | x | y | left z = left (λ {(tif xx then yy else zz) -> z zz})
check Δ Γ t0 (Base NN) = right t0
check Δ Γ t0 (Base BB) = left (λ ())
check Δ Γ t0 (A ⇒ A₁) = left (λ ())
check Δ Γ (tS t) (Base BB) = left (λ ())
check Δ Γ (tS t) (Base NN) with check Δ Γ t (Base NN)
... | just t' = just (tS t')
... | left p = left (λ {(tS t) -> p t})
check Δ Γ (tS t) (A ⇒ A₁) = left (λ ())
check Δ Γ (tNrec n a b) A with check Δ Γ n (Base NN) | check Δ Γ a A | check Δ Γ b (A ⇒ A)
... | just n' | just a' | just b' = right (tNrec n' a' b')
... | left n' | a' | b' = left (λ {(tNrec nn aa bb) -> n' nn})
... | n' | left a' | b' = left (λ {(tNrec nn aa bb) -> a' aa})
... | n' | a' | left b' = left (λ {(tNrec nn aa bb) -> b' bb})
check Δ Γ (fvar x) A with checkFVar Γ A x
... | just (p) = just (fvar p)
... | left p = left (λ {(fvar xx) -> p xx})
check Δ Γ (bvar x) A with checkBVar Δ A x
... | just (p) = just (bvar p)
... | left p = left (λ {(bvar xx) -> p xx})
check Δ Γ (APP x) A with syn Δ Γ x
... | left p = left (λ {(APP xx) -> p (_ , xx)})
... | just (A' , x') with decideTypeEq A A'
... | just refl-StrId = right (APP x')
... | left p = left (λ {(APP x'') -> p (uniqueAPP x'' x')})
check Δ G (Λ t) (Base x) = left (λ ())
check Δ G (Λ t) (A ⇒ B) with check Δ (G ,, A) t B
... | just x = right (Λ x)
... | left x = left (λ {(Λ xx) -> x xx})



checkIntoTTerm : ∀ Δ Γ A -> (t : Term) -> Maybe (Δ ∣ Γ ⊢ A)
checkIntoTTerm Δ Γ A t with check Δ Γ t A
... | just x = just (AnnToTTerm x)
... | left e = nothing


-- composing type checking with evaluation
checkAndEval : ∀ Δ A t -> Maybe (evalT A)
checkAndEval Δ A t with checkIntoTTerm Δ [] A t
... | just x = just (eval tt x)
... | nothing = nothing

forget = TTermToTerm


--------------------------------------------------------------------
-- Proof that checking is partially inverse to forgetting

pi : ∀ {Δ Γ A t} -> (x : Δ ∣ Γ ⊢ A / t) -> check Δ Γ t A ≣ just x


synpiFVar : ∀{Γ A t} -> (x : Γ ∣πF A / t) -> synFVar Γ t ≣ just (A , x)
synpiFVar {.(_ ,, A)} {A} {zero} zero = refl-StrId
synpiFVar {(Γ ,, B)} {A} {suc t} (suc x) with synFVar Γ t | synpiFVar x
... | .(just (A , x)) | refl-StrId = refl-StrId

synpiBVar : ∀{Δ A t} -> (x : Δ ∣πB A / t) -> synBVar Δ t ≣ just (A , x)
synpiBVar {.(_ ,, _)} {A} {zero} zero = refl-StrId
synpiBVar {(Δ ,, B)} {A} {suc t} (suc x) with synBVar Δ t | synpiBVar x
... | .(just (A , x)) | refl-StrId = refl-StrId

piFVar : ∀{Γ A t} -> (x : Γ ∣πF A / t) -> checkFVar Γ A t ≣ just x
piFVar {Γ} {A} {t} x with synFVar Γ t | synpiFVar x
... | .(just (A , x)) | refl-StrId with decideTypeEq A A | decideTypeEq-id A
... | .(just refl-StrId) | refl-StrId = refl-StrId

piBVar : ∀{Δ A t} -> (x : Δ ∣πB A / t) -> checkBVar Δ A t ≣ just x
piBVar {Δ} {A} {t} x with synBVar Δ t | synpiBVar x
... | .(just (A , x)) | refl-StrId with decideTypeEq A A | decideTypeEq-id A
... | .(just refl-StrId) | refl-StrId = refl-StrId

synpiAPP : ∀{Δ Γ A t} -> (x : Δ ∣ Γ ⊢APP A / t) -> syn Δ Γ t ≣ just (A , x)
synpiAPP {Δ} {Γ} {A} {app t x₁} (app {A₁} x x₂) with syn Δ Γ t | synpiAPP x
... | .(just (A₁ ⇒ A , x)) | refl-StrId with check Δ Γ x₁ A₁ | pi x₂
... | .(just x₂) | refl-StrId = refl-StrId
synpiAPP {Δ} {Γ} {A} {fvar x₁} (fvar x) with synFVar Γ x₁ | synpiFVar x
... | .(just (A , x)) | refl-StrId = refl-StrId
synpiAPP {Δ} {Γ} {A} {bvar x₁} (bvar x) with synBVar Δ x₁ | synpiBVar x
... | .(just (A , x)) | refl-StrId = refl-StrId

pi {Δ} {Γ} {.(Base BB)} {tB x₁} (tB .x₁) = refl-StrId
pi {Δ} {Γ} {A} {tif t then t₁ else t₂} (tif x then x₁ else x₂) with check Δ Γ t (Base BB) | check Δ Γ t₁ A | check Δ Γ t₂ A | pi x | pi x₁ | pi x₂
... | .(just x) | .(just x₁) | .(just x₂) | refl-StrId | refl-StrId | refl-StrId = refl-StrId
pi {Δ} {Γ} {.(Base NN)} {t0} t0 = refl-StrId
pi {Δ} {Γ} {A} {tS t} (tS x) with check Δ Γ t (Base NN) | pi x
... | .(just x) | refl-StrId = refl-StrId
pi {Δ} {Γ} {A} {tNrec t t₁ t₂} (tNrec x x₁ x₂) with check Δ Γ t (Base NN) | check Δ Γ t₁ A | check Δ Γ t₂ (A ⇒ A) | pi x | pi x₁ | pi x₂
... | .(just x) | .(just x₁) | .(just x₂) | refl-StrId | refl-StrId | refl-StrId = refl-StrId
pi {Δ} {Γ} {A} {fvar t} (fvar x) with checkFVar Γ A t | piFVar x
... | .(just x) | refl-StrId = refl-StrId
pi {Δ} {Γ} {A} {bvar t} (bvar x) with checkBVar Δ A t | piBVar x
... | .(just x) | refl-StrId = refl-StrId
pi {Δ} {Γ} {A} {APP t} (APP x) with syn Δ Γ t | synpiAPP x
... | .(just (A , x)) | refl-StrId with decideTypeEq A A | decideTypeEq-id A
... | .(just refl-StrId) | refl-StrId = refl-StrId
pi {Δ} {Γ} {(A ⇒ B)} {Λ t} (Λ x) with check Δ (Γ ,, A) t B | pi x
... | .(just x) | refl-StrId = refl-StrId



--------------------------------------------------------------------
-- testing typechecking

-- This rightfully does not typecheck
checkerror : (checkAndEval [] (Base NN ⇒ Base BB) (Λ (fvar zero))) ≣ nothing
checkerror = refl-StrId


-- The nat example from before, but this time with untyped terms.
-- calling 'checkAndEval' on them, results in the correct evaluated Agda terms.

add' : Term
add' = Λ (Λ (tNrec (fvar (suc zero)) (fvar zero) (Λ (tS (fvar zero)))))

checkadd' : (checkAndEval [] (Base NN ⇒ Base NN ⇒ Base NN) add') ≣ just (λ a b → execTimes a (λ x → suc x) b)
checkadd' = refl-StrId

mult' : Term
mult' = Λ (Λ (tNrec (fvar (suc zero)) (t0) (Λ (APP (app (app (bvar zero) (fvar zero)) (fvar (suc zero)))))))

checkmult' : (checkAndEval ([] ,, add) (Base NN ⇒ Base NN ⇒ Base NN) mult') ≣ just (λ a a₁ → execTimes a (λ a₂ → execTimes a₂ (λ a₃ → suc a₃) a₁) 0)
checkmult' = refl-StrId






