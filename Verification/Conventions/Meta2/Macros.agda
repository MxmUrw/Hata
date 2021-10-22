
module Verification.Conventions.Meta2.Macros where

-- open import Verification.Conventions hiding (′_′) public
open import Verification.Conventions.Meta2.Structure public

open import Verification.Conventions.Meta.Term
open import Verification.Conventions.Meta.Universe
open import Verification.Conventions.Prelude hiding (′_′)
-- open import Verification.Conventions.Proprelude

pattern _since_ a b = ′ a ′ {{b}}


module _ {A : 𝒰 𝑖} where
  UniverseHintWrapper : A -> A
  UniverseHintWrapper x = x

isUniverse : Term -> Bool
isUniverse (agda-sort s) = true
isUniverse (def (quote 𝒰') _) = true
isUniverse (def (quote 𝒰) _) = true
isUniverse (def (quote 𝒰₀) _) = true
isUniverse (def (quote 𝒰₁) _) = true
isUniverse (def (quote 𝒰₂) _) = true
isUniverse (def (quote UniverseHintWrapper) _) = true
isUniverse (pi _ _) = true
isUniverse _ = false


#structureOn-impl : Term -> Term -> TC 𝟙-𝒰
#structureOn-impl value hole = do
    Ty <- inferType hole
    -- Ty <- reduce Ty
    -- value <- normalise value
    let Res = if isUniverse Ty
                 then value
                 else con (quote (′_′)) (arg (arg-info visible (modality relevant quantity-ω)) value ∷ [])
    -- let Fun = 
    unify hole Res

-- macro
callWithQuote : Name -> Term -> TC Term
callWithQuote fun ar = do
  -- ar <- normalise ar
  ar <- quoteTC ar
  return (def fun (varg ar ∷ []))

-- macro
--   #structureOn : Term -> Term -> TC 𝟙-𝒰
--   #structureOn value hole = callWithQuote (quote #structureOn-impl) value >>= unify hole

#structureOn : {A : 𝒰 𝑖} (a : A) -> Term -> TC 𝟙-𝒰
#structureOn a hole = do
  a <- quoteTC a
  #structureOn-impl a hole

SomeStructure : 𝒰₀
SomeStructure = Term -> TC 𝟙-𝒰


    -- unify hole cal

    -- (#callWithQuote #shortName value)
    -- val' <- quoteTC value
    -- unify hole (def (quote #shortName) (varg val' ∷ []))

-- macro
--   #short : Term -> Term -> TC 𝟙-𝒰
--   #short value hole = do
--     val' <- quoteTC value
--     unify hole (def (quote #shortName) (varg val' ∷ []))

-- macro
--   mUNIFY : (𝑖 : 𝔏 ^ 3) -> Term -> TC 𝟙-𝒰
--   mUNIFY 𝑖 hole = do
--     Val <- quoteTC (UnificationProblem 𝑖)
--     let Fun = con (quote (′_′)) (arg (arg-info visible (modality relevant quantity-ω)) Val ∷ [])
--     unify hole Fun




infixr 20 _[_]→_
_[_]→_ : ∀{𝑗} (X : 𝒰 𝑗) -> ∀ (𝑖 : 𝔏 ^ 2) -> (R : 𝒰 𝑙) -> (𝒰 _)
_[_]→_ {𝑗 = 𝑗} X 𝑖 R = {U : 𝒰 (𝑖 ⌄ 0)} -> (u : UniverseHintWrapper U) -> {{UU : hasU U (𝑗) (𝑖 ⌄ 1)}} -> {{p : getU UU ≡-Str (X)}} -> R

-- WithStructureOnω : (X : 𝒰 𝑗) -> (R : 𝒰ω) -> (𝒰ω)
-- WithStructureOnω {𝑗} X R = ∀{𝑖 𝑘} -> {U : 𝒰 𝑖} -> (u : U) -> {{UU : hasU U (𝑗) 𝑘}} -> {{p : getU UU ≡-Str (X)}} -> R

infixr 20 λstr-syntax
λstr-syntax : ∀{𝑖 : 𝔏 ^ 2} -> ∀{X : 𝒰 𝑗} {R : 𝒰 𝑙} -> {U : 𝒰 (𝑖 ⌄ 0)} -> (X -> R) -> (u : U) -> {{UU : hasU U (𝑗) (𝑖 ⌄ 1)}} -> {{p : getU UU ≡-Str (X)}} -> R
λstr-syntax f u {{UU}} {{refl-StrId}} = f (destructEl UU u)

syntax λstr-syntax (λ x -> F) = λstr x ↦ F



-------------------------------------------------------------------------------
-- anonymous terms via registering and types


-- registering terms

record Register (A : 𝒰 𝑖) (t : String) : 𝒰 (𝑖 ⁺) where
  constructor register
  field registered : A

open Register public

-- registering with level polymorphism

register-syntax1 : {f : 𝔏 ^ n -> 𝔏} {A : (𝑖 : 𝔏 ^ n) -> 𝒰 (f 𝑖)} (a : ∀ 𝑖 -> A 𝑖) (t : String) -> ∀{𝑖} -> Register (A 𝑖) t
register-syntax1 a t {𝑖} = register (a 𝑖)

syntax register-syntax1 (λ i -> A) t = register₁[ t , i ] A

-- registering without level polymorphism

register-syntax0 : {A : 𝒰 𝑖} (a : A) (t : String) -> Register (A) t
register-syntax0 a t = register a

syntax register-syntax0 A t = register[ t ] A


inst : {f : 𝔏 ^ n -> 𝔏} -> (A : (𝑖 : 𝔏 ^ n) -> 𝒰 (f 𝑖)) -> (t : String) -> {{∀{𝑖} -> Register (A 𝑖) t}} -> ∀ (𝑖 : 𝔏 ^ n) ->  SomeStructure
inst A t {{R}} 𝑖 = #structureOn (registered (R {𝑖}))



instantiate-syntax : {f : 𝔏 ^ n -> 𝔏} -> (A : (𝑖 : 𝔏 ^ n) -> 𝒰 (f 𝑖)) -> (t : String) -> {{∀{𝑖} -> Register (A 𝑖) t}} -> ∀ (𝑖 : 𝔏 ^ n) ->  SomeStructure
instantiate-syntax {f} A t 𝑖 = inst (λ i -> A i) t 𝑖

infix 25 instantiate-syntax
syntax instantiate-syntax (λ i -> A) t = instance[ t , i ] A


_◀ : (A : ∀(𝑖 : 𝔏 ^ n) -> Term -> TC 𝟙-𝒰) -> {𝑖 : 𝔏 ^ n} -> Term -> TC 𝟙-𝒰
_◀ A {𝑖} t = A 𝑖 t


-- instantiate-syntax2 : {f : 𝔏 ^ n -> 𝔏 ^ m -> 𝔏} -> (A : (𝑖 : 𝔏 ^ n) -> (𝑗 : 𝔏 ^ m) -> 𝒰 (f 𝑖 𝑗)) -> (t : String) -> {{∀{𝑖 𝑗} -> Register (A 𝑖 𝑗) t}} -> ∀ (𝑖 : 𝔏 ^ n) -> ∀(𝑗 : 𝔏 ^ m) ->  SomeStructure
-- instantiate-syntax2 {f} A t 𝑖 𝑗 = inst (λ i j -> A i j) t 𝑖 𝑗

instantiate-syntax2 : {f : 𝔏 ^ n -> 𝔏} -> (A : (𝑖 : 𝔏 ^ n) -> 𝒰 (f 𝑖)) -> (t : String) -> {{∀{𝑖} -> Register (A 𝑖) t}} -> ∀ (𝑖 : 𝔏 ^ n) ->  SomeStructure
instantiate-syntax2 {f} A t 𝑖 = inst (λ i -> A i) t 𝑖

infix 25 instantiate-syntax2
syntax instantiate-syntax2 {n = n} (λ i -> A) t = instance[ t , i / n ] A





---------------------------------------------------------------
-- one line definitions (which may contain types) using unquoteDecl

#idefAs-impl : Name -> (A : 𝒰 𝑖) -> (a : A) -> TC 𝟙-𝒰
#idefAs-impl targetName A a = do

  targetType <- quoteTC A
  targetTerm <- quoteTC a

  let targetFun = def targetName []
  let targetFunClause = clause [] [] targetTerm

  declareDef (iarg targetName) targetType
  defineFun targetName (targetFunClause ∷ [])


#idef-impl : Name -> {A : 𝒰 𝑖} -> (a : A) -> TC 𝟙-𝒰
#idef-impl targetName {A} a = #idefAs-impl targetName A a


infix 1 #idef-impl #idefAs-impl
syntax #idef-impl name a = #idef name := a
syntax #idefAs-impl name A a = #idef name ∶ A := a
