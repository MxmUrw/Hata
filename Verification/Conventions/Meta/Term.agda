

module Verification.Conventions.Meta.Term where

open import Verification.Conventions.Prelude hiding (𝑖 ; 𝑗 ; 𝑘 ; 𝑙)
open import Agda.Builtin.Reflection public
open import Agda.Builtin.Char

open PrimitiveUniverseNotation

{-# TERMINATING #-}
cmpTerm : Term -> Term -> Bool

instance
  IBootEq:Term : IBootEq Term
  IBootEq._≟_ IBootEq:Term = cmpTerm

instance
  IBootEq:Name : IBootEq Name
  IBootEq._≟_ IBootEq:Name = primQNameEquality

  IBootEq:Meta : IBootEq Meta
  IBootEq._≟_ IBootEq:Meta = primMetaEquality

instance
  IBootEq:Visibility : IBootEq Visibility
  IBootEq._≟_ IBootEq:Visibility = _≟V_
    where
      _≟V_ : Visibility -> Visibility -> Bool
      visible ≟V visible = true
      hidden ≟V hidden = true
      instance′ ≟V instance′ = true
      _ ≟V _ = false


instance
  IBootEq:Relevance : IBootEq Relevance
  (IBootEq:Relevance IBootEq.≟ relevant) relevant = true
  (IBootEq:Relevance IBootEq.≟ relevant) irrelevant = false
  (IBootEq:Relevance IBootEq.≟ irrelevant) relevant = false
  (IBootEq:Relevance IBootEq.≟ irrelevant) irrelevant = true

  IBootEq:Quantity : IBootEq Quantity
  IBootEq._≟_ IBootEq:Quantity quantity-0 quantity-0 = true
  IBootEq._≟_ IBootEq:Quantity quantity-0 quantity-ω = false
  IBootEq._≟_ IBootEq:Quantity quantity-ω quantity-0 = false
  IBootEq._≟_ IBootEq:Quantity quantity-ω quantity-ω = true


  IBootEq:Modality : IBootEq Modality
  IBootEq._≟_ IBootEq:Modality (modality r1 q1) (modality r2 q2) = (r1 ≟ r2) and (q1 ≟ q2)


instance
  IBootEq:ArgInfo : IBootEq ArgInfo
  (IBootEq:ArgInfo IBootEq.≟ arg-info v r) (arg-info w s) = (v ≟ w) and (r ≟ s)

  IBootEq:Arg : ∀{A : 𝒰 𝑖} -> {{_ : IBootEq A}} -> IBootEq (Arg A)
  (IBootEq:Arg IBootEq.≟ arg i x) (arg j y) = (i ≟ j) and (x ≟ y)

  IBootEq:Abs : ∀{A : 𝒰 𝑖} -> {{_ : IBootEq A}} -> IBootEq (Abs A)
  (IBootEq:Abs IBootEq.≟ Abs.abs s x) (Abs.abs t y) = x ≟ y -- WARNING! We do ignore the strings here, because they should not be relevant

  IBootEq:Literal : IBootEq Literal
  (IBootEq:Literal IBootEq.≟ nat n) (nat m) = n ≟ m
  (IBootEq:Literal IBootEq.≟ word64 n) (word64 m) = n ≟ m
  (IBootEq:Literal IBootEq.≟ float x) (float y) = x ≟ y
  (IBootEq:Literal IBootEq.≟ char c) (char d) = c ≟ d
  (IBootEq:Literal IBootEq.≟ string s) (string t) = s ≟ t
  (IBootEq:Literal IBootEq.≟ name x) (name y) = x ≟ y
  (IBootEq:Literal IBootEq.≟ meta x) (meta y) = x ≟ y
  (IBootEq:Literal IBootEq.≟ _) (_) = false


  IBootEq:Pattern : IBootEq Pattern
  (IBootEq:Pattern IBootEq.≟ con c ps) (con d ps2) = (c ≟ d) and (ps ≟ ps2)
  (IBootEq:Pattern IBootEq.≟ dot t) (dot s) = t ≟ s
  (IBootEq:Pattern IBootEq.≟ var x) (var y) = x ≟ y
  (IBootEq:Pattern IBootEq.≟ lit l) (lit m) = l ≟ m
  (IBootEq:Pattern IBootEq.≟ proj f) (proj g) = f ≟ g
  (IBootEq:Pattern IBootEq.≟ absurd x) (absurd y) = true -- WARNING! We ignore the x : ℕ argument here, though I do not know what it means. (But it seems irrelevant)
  (IBootEq:Pattern IBootEq.≟ _) (_) = false

  IBootEq:Clause : IBootEq Clause
  (IBootEq:Clause IBootEq.≟ clause tel ps t) (clause tel2 ps2 t2) = (map-List snd tel ≟ map-List snd tel2) and (ps ≟ ps2) and (t ≟ t2)
  (IBootEq:Clause IBootEq.≟ absurd-clause tel ps) (absurd-clause tel2 ps2) = (map-List snd tel ≟ map-List snd tel2) and (ps ≟ ps2)
  (IBootEq:Clause IBootEq.≟ _) (_) = false

  IBootEq:Sort : IBootEq Sort
  (IBootEq:Sort IBootEq.≟ set s) (set t) = s ≟ t
  (IBootEq:Sort IBootEq.≟ lit n) (lit m) = n ≟ m
  (IBootEq:Sort IBootEq.≟ unknown) unknown = true
  (IBootEq:Sort IBootEq.≟ _) _ = false




cmpTerm (var x args) (var y args2) = (x ≟ y) and (args ≟ args2)
cmpTerm (con c args) (con d args2) = (c ≟ d) and (args ≟ args2)
cmpTerm (def f args) (def g args2) = (f ≟ g) and (args ≟ args2)
cmpTerm (lam v t) (lam w s) = (v ≟ w) and (t ≟ s)
cmpTerm (pat-lam cs args) (pat-lam ds args2) = (cs ≟ ds) and (args ≟ args2)
cmpTerm (pi a b) (pi a2 b2) = (a ≟ a2) and (b ≟ b2)
cmpTerm (agda-sort s) (agda-sort t) = s ≟ t
cmpTerm (lit l) (lit m) = l ≟ m
cmpTerm (meta x y) (meta x2 y2) = (x ≟ x2) and (y ≟ y2)
cmpTerm unknown unknown = true
cmpTerm _ _ = false


assertType : ∀(a : 𝒰' 𝑖) -> TC a -> TC a
assertType _ x = x



showImplicit = false

wrapVis : Visibility -> String -> String
wrapVis visible s = "(" <> s <> ")"
wrapVis hidden s with showImplicit
... | true = "{" <> s <> "}"
... | false = ""
wrapVis instance′ s = "{{" <> s <> "}}"

wrapRel : Relevance -> String -> String
wrapRel relevant s = s
wrapRel irrelevant s = "." <> s

wrapMod : Modality -> String -> String
wrapMod m s = s
-- wrapMod relevant s = s
-- wrapMod irrelevant s = "." <> s

wrapInfo : ArgInfo -> String -> String
wrapInfo (arg-info v r) s = wrapVis v (wrapMod r s)


instance
  IShow:Arg : ∀{A : 𝒰 𝑖} -> {{_ : IShow A}} -> IShow (Arg A)
  IShow.show IShow:Arg (arg i x) = wrapInfo i (show x)

getFromArg : ∀{A : 𝒰 𝑖} -> Arg A -> A
getFromArg (arg _ a) = a

findMainName : List Char -> List Char -> List Char
findMainName cur [] = cur
findMainName cur ('.' ∷ s) = findMainName [] s
findMainName cur (x ∷ s) = findMainName (cur <> (x ∷ [])) s

instance
  IShow:Name : IShow Name
  IShow.show IShow:Name s = primStringFromList (findMainName [] (primStringToList (primShowQName s)))

instance
  IShow:Meta : IShow Meta
  IShow.show IShow:Meta s = "meta" <> primShowMeta s

showListSpace : ∀{A : 𝒰 𝑖} {{_ : IShow A}} -> List A -> String
showListSpace (xs) with show xs
... | "" = ""
... | t = " " <> t


instance
  {-# TERMINATING #-}
  IShow:Term : IShow Term

  IShow:Sort : IShow Sort
  IShow.show IShow:Sort (set t) = "𝒰 (" <> show t <> ")"
  IShow.show IShow:Sort (lit n) = "𝒰 " <> show n
  IShow.show IShow:Sort unknown = "?"
  IShow.show IShow:Sort (prop t) = "prop"
  IShow.show IShow:Sort (propLit n) = "propLit"
  IShow.show IShow:Sort (inf n) = "inf"

  IShow.show IShow:Term (var x args) = "(var " <> show x <> ")" <> showListSpace args
  IShow.show IShow:Term (con c args) = "ctor:" <> show c <> showListSpace args
  IShow.show IShow:Term (def f args) = show f <> showListSpace args
  IShow.show IShow:Term (lam v (Abs.abs s x)) = "(λ " <> wrapVis v s <> " -> " <> show x <> ")"
  IShow.show IShow:Term (pat-lam cs args) = "<<pat>>"
  IShow.show IShow:Term (pi a (Abs.abs s x)) = "(Π (" <> s <> " : " <> show a <> ") -> " <> show x <> ")"
  IShow.show IShow:Term (agda-sort s) = show s
  IShow.show IShow:Term (lit l) = "<<literal>>"
  IShow.show IShow:Term (meta x args) = show x <> showListSpace args
  IShow.show IShow:Term unknown = "?"

  IShow:Pattern : IShow Pattern
  IShow.show IShow:Pattern (con c ps) = "<<constr pattern>>"
  IShow.show IShow:Pattern (dot t) = "." <> show t
  IShow.show IShow:Pattern (var x) = "(var" <> show x <> ")"
  IShow.show IShow:Pattern (lit l) = "<<literal pattern>>"
  IShow.show IShow:Pattern (proj f) = "<< proj pattern >>"
  IShow.show IShow:Pattern (absurd _) = "()"

_≟S_ = primStringEquality

_++_ = primStringAppend

infixl 40 _>>=_
_>>=_ = bindTC
return = returnTC
_>>_ : ∀{A B : 𝒰 𝑖} -> (TC A) -> TC B -> TC B
_>>_ a b = a >>= \_ -> b

-- pattern varg x = arg (arg-info visible relevant) x
-- pattern harg x = arg (arg-info hidden  relevant) x
-- pattern iarg x = arg (arg-info instance′    relevant) x

pattern varg x = arg (arg-info visible (modality relevant quantity-ω)) x
pattern harg x = arg (arg-info hidden  (modality relevant quantity-ω)) x
pattern iarg x = arg (arg-info instance′    (modality relevant quantity-ω)) x

printErr : ∀{A : 𝒰 𝑖} -> String -> TC A
printErr s = typeError (strErr s ∷ [])

printType : ∀{A : 𝒰 𝑖} -> Type -> TC A
printType τ = typeError (termErr τ ∷ [])

open TypeNotation public



-- Maybe : 𝒰 𝑖 -> 𝒰 𝑖
-- Maybe A = ⊤ +-𝒰 A

-- pattern just x = right x
-- pattern nothing = left tt

map-Arg : ∀{A B : 𝒰 𝑖} -> (A -> B) -> Arg A -> Arg B
map-Arg f (arg i x) = arg i (f x)


-- map-Maybe : ∀{A B : 𝒰 𝑖} -> (A -> B) -> Maybe A -> Maybe B
-- map-Maybe f (left x) = left x
-- map-Maybe f (right x) = right (f x)

map-Abs : ∀{A B : 𝒰 𝑖} -> (A -> B) -> Abs A -> Abs B
map-Abs f (Abs.abs s x) = Abs.abs s (f x)

liftArgs : List (Arg ℕ) -> List (Arg ℕ)
liftArgs = map-List (map-Arg suc)

_≤?_ : ℕ -> ℕ -> Bool
zero ≤? j = true
suc i ≤? zero = false
suc i ≤? suc j = i ≤? j

-- === Lowering

lowerAbove : ℕ -> ℕ -> ℕ
lowerAbove i j with i ≤? j
... | false = j
lowerAbove i zero | true = zero
lowerAbove i (suc j) | true = j

lowerAt : ℕ -> Type -> Type

{-# TERMINATING #-}
lowerAtVar : ℕ -> ℕ × List (Arg Term) -> ℕ × List (Arg Term)
lowerAtVar i (j , ts) = lowerAbove i j , map-List (map-Arg (lowerAt i)) ts

lowerAtSort : ℕ -> Sort -> Sort
lowerAtSort i (set t) = set (lowerAt i t)
lowerAtSort i (lit n) = lit n
lowerAtSort i unknown = unknown
lowerAtSort i (prop t) = prop (lowerAt i t)
lowerAtSort i (propLit n) = propLit n
lowerAtSort i (inf n) = inf n

lowerAt i (var x args) = let (x , args) = lowerAtVar i (x , args) in var x args
lowerAt i (con c args) = con c (map-List (map-Arg (lowerAt i)) args)
lowerAt i (def f args) = def f (map-List (map-Arg (lowerAt i)) args)
lowerAt i (lam v t) = lam v (map-Abs (lowerAt (suc i)) t)
lowerAt i (pat-lam cs args) = unknown
lowerAt i (pi a b) = pi (map-Arg (lowerAt i) a) (map-Abs (lowerAt (suc i)) b)
lowerAt i (agda-sort s) = agda-sort (lowerAtSort i s)
lowerAt i (lit l) = lit l
lowerAt i (meta x y) = unknown
lowerAt i unknown = unknown

-- === Lifting

liftBelow : ℕ -> ℕ -> ℕ
liftBelow i j with suc j ≤? i
... | false = j
... | true = suc j

liftFromTill : ℕ -> ℕ -> Type -> Type

{-# TERMINATING #-}
liftFromTillVar : ℕ -> ℕ -> ℕ × List (Arg Term) -> ℕ × List (Arg Term)
liftFromTillVar k i (j , ts) = liftBelow i j , map-List (map-Arg (liftFromTill k i)) ts

liftFromTillSort : ℕ -> ℕ -> Sort -> Sort
liftFromTillSort k i (set t) = set (liftFromTill k i t)
liftFromTillSort k i (lit n) = lit n
liftFromTillSort k i unknown = unknown
liftFromTillSort k i (prop t) = prop (liftFromTill k i t)
liftFromTillSort k i (propLit n) = propLit n
liftFromTillSort k i (inf n) = inf n

liftFromTill k i (var x args) = let (x , args) = liftFromTillVar k i (x , args) in var x args
liftFromTill k i (con c args) = con c (map-List (map-Arg (liftFromTill k i)) args)
liftFromTill k i (def f args) = def f (map-List (map-Arg (liftFromTill k i)) args)
liftFromTill k i (lam v t) = lam v (map-Abs (liftFromTill (suc k) i) t)
liftFromTill k i (pat-lam cs args) = unknown
liftFromTill k i (pi a b) = pi (map-Arg (liftFromTill k i) a) (map-Abs (liftFromTill (suc k) i) b)
liftFromTill k i (agda-sort s) = agda-sort (liftFromTillSort k i s)
liftFromTill k i (lit l) = lit l
liftFromTill k i (meta x y) = unknown
liftFromTill k i unknown = unknown

liftTill : ℕ -> Type -> Type
liftTill = liftFromTill 0

liftTillSort : ℕ -> Sort -> Sort
liftTillSort = liftFromTillSort 0

-- == Lifting from a value

liftAbove : ℕ -> ℕ -> ℕ
liftAbove i j with i ≤? j
... | false = j
... | true = suc j

liftFrom : ℕ -> Type -> Type

{-# TERMINATING #-}
liftFromVar : ℕ -> ℕ × List (Arg Term) -> ℕ × List (Arg Term)
liftFromVar i (j , ts) = liftAbove i j , map-List (map-Arg (liftFrom i)) ts

liftFromSort : ℕ -> Sort -> Sort
liftFromSort i (set t) = set (liftFrom i t)
liftFromSort i (lit n) = lit n
liftFromSort i unknown = unknown
liftFromSort i (prop t) = prop (liftFrom i t)
liftFromSort i (propLit n) = propLit n
liftFromSort i (inf n) = inf n

liftFrom i (var x args) = let (x , args) = liftFromVar i (x , args) in var x args
liftFrom i (con c args) = con c (map-List (map-Arg (liftFrom i)) args)
liftFrom i (def f args) = def f (map-List (map-Arg (liftFrom i)) args)
liftFrom i (lam v t) = lam v (map-Abs (liftFrom (suc i)) t)
liftFrom i (pat-lam cs args) = unknown
liftFrom i (pi a b) = pi (map-Arg (liftFrom i) a) (map-Abs (liftFrom (suc i)) b)
liftFrom i (agda-sort s) = agda-sort (liftFromSort i s)
liftFrom i (lit l) = lit l
liftFrom i (meta x y) = unknown
liftFrom i unknown = unknown

liftPat : Pattern -> Pattern
liftPat (var x) = var (suc x)
liftPat (con c ps) = (absurd 0)
liftPat (dot t) = absurd 0
liftPat (lit l) = lit l
liftPat (proj f) = absurd 0
liftPat (absurd _) = absurd 0

liftPats : List (Arg Pattern) -> List (Arg Pattern)
liftPats = map-List (map-Arg liftPat)


-- === Unbound lifiting of many

-- lowerAbove : ℕ -> ℕ -> ℕ
-- lowerAbove i j with i ≤? j
-- ... | false = j
-- lowerAbove i zero | true = zero
-- lowerAbove i (suc j) | true = j

liftMany : ℕ -> Type -> Type

{-# TERMINATING #-}
liftManyVar : ℕ -> ℕ × List (Arg Term) -> ℕ × List (Arg Term)
liftManyVar i (j , ts) = i +-ℕ j , map-List (map-Arg (liftMany i)) ts

liftManySort : ℕ -> Sort -> Sort
liftManySort i (set t) = set (liftMany i t)
liftManySort i (lit n) = lit n
liftManySort i unknown = unknown
liftManySort i (prop t) = prop (liftMany i t)
liftManySort i (propLit n) = propLit n
liftManySort i (inf n) = inf n

liftMany i (var x args) = let (x , args) = liftManyVar i (x , args) in var x args
liftMany i (con c args) = con c (map-List (map-Arg (liftMany i)) args)
liftMany i (def f args) = def f (map-List (map-Arg (liftMany i)) args)
liftMany i (lam v t) = lam v (map-Abs (liftMany (i)) t)
liftMany i (pat-lam cs args) = unknown
liftMany i (pi a b) = pi (map-Arg (liftMany i) a) (map-Abs (liftMany (i)) b)
liftMany i (agda-sort s) = agda-sort (liftManySort i s)
liftMany i (lit l) = lit l
liftMany i (meta x y) = unknown
liftMany i unknown = unknown

--

first : {A B C : 𝒰 𝑖} -> (A -> C) -> (A × B) -> (C × B)
first f (a , b) = f a , b

second : {A B C : 𝒰 𝑖} -> (B -> C) -> (A × B) -> (A × C)
second f (a , b) = a , f b

insertList : ∀{A : 𝒰 𝑖} -> ℕ -> A -> List A -> List A
insertList zero a xs = a ∷ xs
insertList (suc i) a [] = []
insertList (suc i) a (x ∷ xs) = x ∷ insertList i a xs

liftTCMaybe : ∀{A : 𝒰 𝑖} -> Maybe A -> String -> TC A
liftTCMaybe (left x) s = printErr s
liftTCMaybe (just x) s = return x

η : ∀{A : 𝒰 𝑖} -> A -> List A
η a = a ∷ []

μ : ∀{A : 𝒰 𝑖} -> List (List A) -> List A
μ [] = []
μ (a ∷ as) = a <> μ as


-- == getting (free?) variables

lowerVars : List ℕ -> List ℕ
lowerVars [] = []
lowerVars (zero ∷ xs) = lowerVars xs
lowerVars (suc x ∷ xs) = x ∷ lowerVars xs


{-# TERMINATING #-}
getVars : Visibility -> Type -> List ℕ

getVarsArg : Visibility -> Arg Term -> List ℕ
getVarsArg v (arg (arg-info w _) x) with v ≟ w
... | true = getVars v x
... | false = []

getVarsSort : Visibility -> Sort -> List ℕ
getVarsSort v (set t) = getVars v t
getVarsSort v (lit n) = []
getVarsSort v unknown = []
getVarsSort v (prop t) = getVars v t
getVarsSort v (propLit n) = []
getVarsSort v (inf n) = []

getVars v (var x args) = η x <> μ (map-List (getVarsArg v) args)
getVars v (con c args) = μ (map-List (getVarsArg v) args)
getVars v (def f args) = μ (map-List (getVarsArg v) args)
getVars v (lam τ t) = []
getVars v (pat-lam cs args) = []
getVars v (pi (arg i x) (Abs.abs _ b)) = getVars v x <> (lowerVars (getVars v b))
getVars v (agda-sort s) = getVarsSort v s
getVars v (lit l) = []
getVars v (meta x x₁) = []
getVars v unknown = []

-- == replacing

SSub = ℕ × (List (Arg Term) -> Type)

jumpOverAbs : SSub -> SSub
jumpOverAbs (i , τ) = (suc i , (λ args -> liftMany 1 (τ args)))

-- replaceNat : SSub -> ℕ -> Type

replace : SSub -> Type -> Type

{-# TERMINATING #-}
replaceVar : SSub -> ℕ × List (Arg Term) -> Term
replaceVar (i , τ) (j , args) with i ≟-ℕ j
... | eq _ = τ (map-List (map-Arg (replace (i , τ))) args)
... | _ = var j (map-List (map-Arg (replace (i , τ))) args)
-- replaceVar i (j , ts) = {!!} -- replaceNat i j , map-List (map-Arg (replace i)) ts

replaceSort : SSub -> Sort -> Sort
replaceSort i (set t) = set (replace i t)
replaceSort i (lit n) = lit n
replaceSort i unknown = unknown
replaceSort i (prop t) = prop (replace i t)
replaceSort i (propLit n) = propLit n
replaceSort i (inf n) = inf n

replace i (var x args) = replaceVar i (x , args)
replace i (con c args) = con c (map-List (map-Arg (replace i)) args)
replace i (def f args) = def f (map-List (map-Arg (replace i)) args)
replace i (lam v t) = lam v (map-Abs (replace (jumpOverAbs i)) t)
replace i (pat-lam cs args) = unknown
replace i (pi a b) = pi (map-Arg (replace i) a) (map-Abs (replace (jumpOverAbs i)) b)
replace i (agda-sort s) = agda-sort (replaceSort i s)
replace i (lit l) = lit l
replace i (meta x y) = unknown
replace i unknown = unknown


-- == substituting


tesubst : SSub -> Type -> Type


{-# TERMINATING #-}
tesubstVar : SSub -> ℕ × List (Arg Term) -> Term
tesubstVar (i , τ) (j , args) with i ≟-ℕ j
... | eq _ = τ (map-List (map-Arg (tesubst (i , τ))) args)
... | gt _ = var j (map-List (map-Arg (tesubst (i , τ))) args)
... | lt p = var (predℕ j) (map-List (map-Arg (tesubst (i , τ))) args)
-- ... | _ = var j (map-List (map-Arg (tesubst (i , τ))) args)
-- tesubstVar i (j , ts) = {!!} -- tesubstNat i j , map-List (map-Arg (tesubst i)) ts

tesubstSort : SSub -> Sort -> Sort
tesubstSort i (set t) = set (tesubst i t)
tesubstSort i (lit n) = lit n
tesubstSort i unknown = unknown
tesubstSort i (prop t) = prop (tesubst i t)
tesubstSort i (propLit n) = propLit n
tesubstSort i (inf n) = inf n

tesubst i (var x args) = tesubstVar i (x , args)
tesubst i (con c args) = con c (map-List (map-Arg (tesubst i)) args)
tesubst i (def f args) = def f (map-List (map-Arg (tesubst i)) args)
tesubst i (lam v t) = lam v (map-Abs (tesubst (jumpOverAbs i)) t)
tesubst i (pat-lam cs args) = unknown
tesubst i (pi a b) = pi (map-Arg (tesubst i) a) (map-Abs (tesubst (jumpOverAbs i)) b)
tesubst i (agda-sort s) = agda-sort (tesubstSort i s)
tesubst i (lit l) = lit l
tesubst i (meta x y) = unknown
tesubst i unknown = unknown



