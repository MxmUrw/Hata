
module Verification.Experimental.Conventions where

open import Verification.Conventions hiding (′_′) public
open import Verification.Experimental.Meta.Structure public

open import Verification.Conventions.Meta.Term

pattern _since_ a b = ′ a ′ {{b}}


isUniverse : Term -> Bool
isUniverse (agda-sort s) = true
isUniverse (def (quote 𝒰) _) = true
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
_[_]→_ {𝑗 = 𝑗} X 𝑖 R = {U : 𝒰 (𝑖 ⌄ 0)} -> (u : U) -> {{UU : hasU U (𝑗) (𝑖 ⌄ 1)}} -> {{p : getU UU ≡-Str (X)}} -> R

-- WithStructureOnω : (X : 𝒰 𝑗) -> (R : 𝒰ω) -> (𝒰ω)
-- WithStructureOnω {𝑗} X R = ∀{𝑖 𝑘} -> {U : 𝒰 𝑖} -> (u : U) -> {{UU : hasU U (𝑗) 𝑘}} -> {{p : getU UU ≡-Str (X)}} -> R

infixr 20 λstr-syntax
λstr-syntax : ∀{𝑖 : 𝔏 ^ 2} -> ∀{X : 𝒰 𝑗} {R : 𝒰 𝑙} -> {U : 𝒰 (𝑖 ⌄ 0)} -> (X -> R) -> (u : U) -> {{UU : hasU U (𝑗) (𝑖 ⌄ 1)}} -> {{p : getU UU ≡-Str (X)}} -> R
λstr-syntax f u {{UU}} {{refl-StrId}} = f (destructEl UU u)

syntax λstr-syntax (λ x -> F) = λstr x ↦ F



-------------------------------------------------------------------------------
-- anonymous terms via registering and types


-- registering terms

record Register {f : 𝔏 ^ n -> 𝔏} (A : (𝑖 : 𝔏 ^ n) -> 𝒰 (f 𝑖)) (t : String) : 𝒰ω where
  constructor register
  field registered : ∀{𝑖} -> A 𝑖

open Register public

register-syntax : {f : 𝔏 ^ n -> 𝔏} {A : (𝑖 : 𝔏 ^ n) -> 𝒰 (f 𝑖)} (a : ∀ 𝑖 -> A 𝑖) (t : String) -> Register A t
register-syntax a t = register (λ {𝑖} -> a 𝑖)

syntax register-syntax (λ i -> A) t = register[ t , i ] A



-- instantiating terms

inst : {f : 𝔏 ^ n -> 𝔏} -> (A : (𝑖 : 𝔏 ^ n) -> 𝒰 (f 𝑖)) -> (t : String) -> {{Register A t}} -> ∀ (𝑖 : 𝔏 ^ n) ->  SomeStructure
inst A t {{R}} 𝑖 = #structureOn (registered R {𝑖})


instantiate-syntax : {f : 𝔏 ^ n -> 𝔏} -> (A : (𝑖 : 𝔏 ^ n) -> 𝒰 (f 𝑖)) -> (t : String) -> {{Register A t}} -> ∀ (𝑖 : 𝔏 ^ n) ->  SomeStructure
instantiate-syntax {f} A t 𝑖 = inst (λ i -> A i) t 𝑖

infix 25 instantiate-syntax
-- syntax instantiate-syntax (λ i -> A) t = A instance[ i , t ]
syntax instantiate-syntax (λ i -> A) t = instance[ t , i ] A

_◀ : (A : ∀(𝑖 : 𝔏 ^ n) -> Term -> TC 𝟙-𝒰) -> {𝑖 : 𝔏 ^ n} -> Term -> TC 𝟙-𝒰
_◀ A {𝑖} t = A 𝑖 t


-- level-syntax : (A : ∀(𝑖 : 𝔏 ^ n) -> Term -> TC 𝟙-𝒰) -> (𝑖 : 𝔏 ^ n) -> Term -> TC 𝟙-𝒰
-- level-syntax A t 𝑖 = A t 𝑖

-- syntax level-syntax (λ i -> A) = withlev i , A

-- F = λ (𝑖 : 𝔏 ^ _) -> inst (λ 𝑖 -> Graph 𝑖 -> Setoid _) "" 𝑖
-- F' = withlev 𝑖 , inst (λ 𝑖 -> Graph 𝑖 -> Setoid _) "" 𝑖
-- F'' = level-syntax (inst (λ 𝑖 -> Graph 𝑖 -> Setoid _) "")


