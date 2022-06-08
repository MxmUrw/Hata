
{-# OPTIONS --cubical --allow-unsolved-metas #-}

module Verification.Conventions.Meta.Structure where

open import Verification.Conventions.Prelude
open import Verification.Conventions.Meta.Term


open PrimitiveUniverseNotation



-- module _ (A : 𝒰 𝑖) where
--   record IField : 𝒰 𝑖 where
--     field -_ : A -> A
--           _+_ : A -> A -> A
--           _*_ : A -> A -> A
--   open IField {{...}} public


private
  module TestStructure where
    record IRing {𝑖 : 𝔏} (A : 𝒰 𝑖) : 𝒰 𝑖 where
      field -_ : A -> A
            _+_ : A -> A -> A
            _*_ : A -> A -> A
    open IRing {{...}} public





-------------------------
-- Teles

Full = (String × Arg (Type × Pattern))

FullTele = List ((String × Arg (Type × Pattern)))
Tele = List (String × Arg Type)


teleFromFullTele : FullTele -> Tele
teleFromFullTele = map-List (second (map-Arg fst))

matchesFromFullTele : FullTele -> List (Arg Pattern)
matchesFromFullTele = map-List (λ (_ , a) -> map-Arg snd a)

makePiType : Tele -> Type -> Type
makePiType [] τ = τ
makePiType ((ar , a) ∷ tele) τ = pi a (Abs.abs ar (makePiType tele τ))

-------------------------
-- making implicit variables visible

intoVisible : ∀{A : 𝒰 𝑖} -> Visibility -> Arg A -> Arg A
intoVisible v (arg (arg-info visible r) x) = arg (arg-info v r) x
intoVisible v (arg (arg-info hidden r) x) = arg (arg-info v r) x
intoVisible v (arg (arg-info instance′ r) x) = arg (arg-info instance′ r) x

makeVisible : Visibility -> ℕ -> FullTele -> FullTele
makeVisible v i tele = rev (makeVisible' i (rev tele))
  where
    makeVisible' : ℕ -> FullTele -> FullTele
    makeVisible' zero [] = []
    makeVisible' zero ((a , ar) ∷ xs) = (a , intoVisible v ar) ∷ xs
    makeVisible' (suc i) [] = []
    makeVisible' (suc i) (x ∷ xs) = x ∷ makeVisible' i xs

makeVisibleMany : Visibility -> List ℕ -> FullTele -> FullTele
makeVisibleMany v [] tele = tele
makeVisibleMany v (n ∷ ns) tele = makeVisibleMany v ns (makeVisible v n tele)

makeVisibleAll : Visibility -> FullTele -> FullTele
makeVisibleAll v tele = map-List (second (intoVisible v)) tele

isUsedInOtherVisibles : ℕ -> FullTele -> String -> Bool
isUsedInOtherVisibles i tele main = isUsedInOtherVisibles' i (rev tele) main
  where
    isUsedInOtherVisibles' : ℕ -> FullTele -> String -> Bool
    isUsedInOtherVisibles' i [] main = false
    isUsedInOtherVisibles' (zero) _ _ = false -- ((a , ar) ∷ tele) main with a ≟ main
    isUsedInOtherVisibles' (suc i) ((a , ar) ∷ tele) main with a ≟ main
    ... | true = isUsedInOtherVisibles' i tele main
    ... | false with i ∈?-List (getVars visible (getFromArg ar .fst))
    ... | true = true
    ... | false = isUsedInOtherVisibles' i tele main

-------------------------
-- merge level variables

isDef : Term -> Name -> Bool
isDef (def f args) n = f ≟ n
isDef x n = false

isDefInTele : (String × Arg (Type × Pattern)) -> Name -> Bool
isDefInTele ((_ , arg i (τ , _))) n = isDef τ n

isVisibleInTele : Full -> Bool
isVisibleInTele (_ , arg (arg-info visible r) _) = true
isVisibleInTele (_ , arg (arg-info hidden r) _) = false
isVisibleInTele (_ , arg (arg-info instance′ r) _) = false

prodInTele : Full -> Full -> Full
prodInTele (xs , arg i (xτ , xpat)) (ys , arg j (yτ , ypat)) = (xs <> "-" <> ys) , (arg i (def (quote _×_) (varg xτ ∷ varg yτ ∷ []) , ypat))

π₁Var : ℕ -> List (Arg Term) -> Term
π₁Var i args = def (quote fst) (varg (var i []) ∷ args)

π₂Var : ℕ -> List (Arg Term) -> Term
π₂Var i args = def (quote snd) (varg (var i []) ∷ args)

-- π₂InTele : Full -> List (Arg Term) -> Term
-- π₂InTele (_ , arg _ (t , _)) args = def (quote snd) args


-- substitution in tele

tesubstPattern : SSub -> Pattern -> Pattern
tesubstPattern (i , τ) (con c ps) = absurd 0
tesubstPattern (i , τ) (dot t) = absurd 0
tesubstPattern (i , τ) (var x) = var (lowerAbove (suc i) x)
tesubstPattern (i , τ) (lit l) = lit l
tesubstPattern (i , τ) (proj f) = proj f
tesubstPattern (i , τ) (absurd a) = absurd a

tesubstFull : SSub -> Full -> Full
tesubstFull σ (s , arg info (a , b)) = (s , arg info (tesubst σ a , tesubstPattern σ b))

tesubstFullTele : SSub -> FullTele -> FullTele
tesubstFullTele σ [] = []
tesubstFullTele σ (x ∷ tele) = tesubstFull σ x ∷ tesubstFullTele (jumpOverAbs σ) tele

replaceFull : SSub -> Full -> Full
replaceFull σ (s , arg info (a , b)) = (s , arg info (replace σ a , b))

replaceFullTele : SSub -> FullTele -> FullTele
replaceFullTele σ [] = []
replaceFullTele σ (x ∷ tele) = replaceFull σ x ∷ replaceFullTele (jumpOverAbs σ) tele

{-# TERMINATING #-}
mergeLevelVars : (FullTele) -> ((ℕ -> Type -> Type) × FullTele)
mergeLevelVars ([]) = ∆ (λ x -> x) , []
mergeLevelVars (x ∷ []) = ∆ (λ x -> x) , x ∷ []
mergeLevelVars (x ∷ y ∷ tele) with isDefInTele x (quote 𝔏) and isDefInTele y (quote Σ) and isVisibleInTele x and isVisibleInTele y
... | false =
  let (τ , tele) = mergeLevelVars (y ∷ tele)
  in τ , (x ∷ tele)
... | true  =
  let (dσ , tele) = mergeLevelVars (tele)
      ntele = prodInTele x y ∷ tesubstFullTele (0 , π₂Var 0) (replaceFullTele (1 , π₁Var 1) tele)
      i0 = length-List tele
      ndσ = λ extra τ -> let i = i0 +-ℕ extra
                         in tesubst (i , π₂Var i) (replace ((suc i) , π₁Var (suc i)) (dσ extra τ))
  in ndσ , ntele



getLevelN : ℕ -> TC Term
getLevelN zero = quoteTC (ℓ₀)
getLevelN (suc i) = do
  l <- (getLevelN i)
  val <- (unquoteTC l)
  quoteTC (val ⁺')

sortIntoLevelTerm : Sort -> TC Term
sortIntoLevelTerm unknown = return unknown
sortIntoLevelTerm (set t) = return t
sortIntoLevelTerm (lit n) = getLevelN n
sortIntoLevelTerm (prop t) = return t
sortIntoLevelTerm (propLit n) = getLevelN n
sortIntoLevelTerm (inf n) = return unknown -- TODO: What do we actually have to do here?


extractSort : Term -> Maybe Sort
extractSort (agda-sort s) = just s
extractSort t = nothing

getLevel : Term -> TC Term
getLevel (agda-sort s) = sortIntoLevelTerm s
getLevel r = printErr ("Expected to find a 𝒰, but found: " <> show r)

getLevelOfType : Term -> TC Term
getLevelOfType t = inferType t >>= normalise >>= getLevel



-- Args:
-- (current debrujin level : ℕ)
-- (main argument to abstract over name : String)
-- (type of IStructure definition : Type)
-- Returns:
-- ( : Type
-- ....
--  sort of the created type : Sort
-- )

-- liftBelowTele : ℕ -> Tele -> Tele
-- liftBelowTele i = ?

readTele : Type -> ℕ × FullTele × List (Arg ℕ) × Type
readTele (pi a (Abs.abs ar b)) with readTele b
... | i , mtel , mte , mty = suc i
                       , (((ar , (map-Arg (\x -> (x , var i)) a))) ∷ mtel)
                       -- , (map-Arg (∆ (suc i)) a ∷ mte)
                       , (map-Arg (∆ (i)) a ∷ mte)
                       , mty
readTele a = 0 , [] , [] , a





buildStruct : String -> Type -> (ℕ × FullTele × List (Arg ℕ) × Maybe (ℕ × Arg Type) × Maybe Sort)
buildStruct mainArg (pi a (Abs.abs ar b)) with (mainArg ≟S ar) | (buildStruct mainArg b)
... | false | i ,  mtel , mte , mainPos , s = (suc i)
                                              -- , (λ τ -> pi a (Abs.abs ar (mty τ)))
                                              -- , (((ar , a) , (map-Arg (∆ (var (i))) a)) ∷ mtel)
                                              , (((ar , (map-Arg (\x -> (x , var i)) a))) ∷ mtel)
                                              , (map-Arg (∆ (suc i)) a ∷ mte)
                                              , map-Maybe (first suc) mainPos
                                              , s
... | true | i , mtel , mte , mainPos , s  = i
                                              -- , (λ τ -> mty τ) -- mty (liftTill i τ))
                                              , mtel
                                              , mte
                                              , (just (0 , (map-Arg (liftMany i) a)))
                                              , (map-Maybe (lowerAtSort i) s)
buildStruct mainArg x = 0 , [] , [] , nothing , (extractSort x)




_`⊔`_ : Term -> Term -> Term
_`⊔`_ `i` `j` =
  let f = quote _⊔_
  in (def f (varg `i` ∷ varg `j` ∷ []))

makeLam : FullTele -> Term -> Term
makeLam [] t = t
makeLam (((s , arg (arg-info v r₁) r)) ∷ tele) t = lam v (Abs.abs s (makeLam tele t))

extractPredicate : Type -> Maybe Type
extractPredicate t = {!!}

-- | Return the universe of the carrier set, as well as the predicate
match-StructureCall : Term -> TC (Term × Term × Term × Term)
match-StructureCall (def (quote Structure) ((arg _ qi) ∷ (arg _ qj) ∷ (arg _ qA) ∷ (arg _ qP) ∷ _)) = return (qi , qj , qA , qP)
  -- printErr ("Found the predicate: " <> show qP)
match-StructureCall s = printErr (show s <> "\nis not a structure on a predicate.")

-- macro
-- a  #openstruct-test : Name -> Term -> TC `𝟙`
-- a  #openstruct-test name-Inst hole =
--     do
--       type-Inst <- getType name-Inst
--       type-Inst <- withReconstructed (return type-Inst)
--       type-Inst <- normalise type-Inst
--       pred-Term <- match-StructureCall type-Inst

--       `ℕ` <- quoteTC ℕ
--       unify hole `ℕ`


macro
  #openstruct : Name -> Term -> TC 𝟙-𝒰
  #openstruct name-Inst hole =
    do
      type-Inst <- getType name-Inst
      type-Inst <- withReconstructed (return type-Inst)
      type-Inst <- normalise type-Inst
      let (i , mtel , mte , res-Type) = readTele type-Inst
      let mtel = makeVisibleAll (hidden) mtel
      let args = mte
      let args = map-List (map-Arg (λ n -> var n [])) args

      -- | Full term for getting a "Structure P" value
      let structure-Term = (def name-Inst args)

      -- | Tele and variable matchlist for function definition
      let tele = teleFromFullTele mtel
      let varmatches = matchesFromFullTele mtel

      -- | Extracting the predicate from the structure call in the result type
      (carrier-level-Term , pred-level-Term , carrier-Type , pred-Term) <- match-StructureCall res-Type

      -- | In a context of all given variables, apply the predicate to the
      -- carrier set, given by ⟨_⟩
      Γ1 <- getContext
      let Γ2 = rev (tele)
      (res-Term , res-Type) <- inContext (Γ1 <> Γ2)
               do
                  carrier-level-Val <- unquoteTC carrier-level-Term
                  pred-level-Val <- unquoteTC pred-level-Term
                  carrier-Type-Val <- unquoteTC carrier-Type
                  pred-Term-Val <- unquoteTC pred-Term

                  structure-Val <- unquoteTC (structure-Term)

                  let Carrier = (⟨_⟩ {carrier-level-Val}
                                     {pred-level-Val}
                                     {carrier-Type-Val}
                                     {pred-Term-Val}
                                     structure-Val)

                  let pred-Type-Val = (carrier-Type-Val -> 𝒰' pred-level-Val)
                  pred-Val <- assertType pred-Type-Val $ unquoteTC pred-Term

                  let istructure-Type-Val = pred-Val Carrier
                  istructure-Type <- quoteTC istructure-Type-Val >>= normalise

                  let istructure-Val = (of_ {carrier-level-Val}
                                        {pred-level-Val}
                                        {carrier-Type-Val}
                                        {pred-Term-Val}
                                        structure-Val)

                  istructure-Term <- quoteTC istructure-Val >>= normalise
                  return (istructure-Term , istructure-Type)

      let fullType = makePiType tele res-Type


      let fun = res-Term
      let StrFun = clause tele varmatches fun

      let term-Inst = pat-lam (StrFun ∷ []) []

      hole-Type <- inferType hole
      unify hole-Type fullType
      unify hole term-Inst
      return tt


      -- `ℕ` <- quoteTC ℕ
      -- unify hole `ℕ`

      {-
      let fullType = makePiType tele resType


      let fun = (def name-Inst args)
      let StrFun = clause tele varmatches fun

      let term-Inst = pat-lam (StrFun ∷ []) []

      hole-Type <- inferType hole
      unify hole-Type fullType
      unify hole term-Inst
      return tt
      -}


module TestInstancing where
  private
    record MyRec (A : 𝒰₀) : 𝒰₀ where
      field invert : A -> A

    open MyRec {{...}}
    getMyRec : (A : 𝒰₀) -> MyRec A
    MyRec.invert (getMyRec A) = \x -> x
    -- instance _ = λ {A} -> getMyRec A
    -- instance _ = #openstruct getMyRec



#struct : String -> Name -> String -> Name -> Name -> TC 𝟙-𝒰
#struct _ name-IStructure mainArg name-Structure name-ctor =
  do
     ``𝟙`` <- quoteTC 𝟙-𝒰
     `tt` <- quoteTC {A = 𝟙-𝒰} tt

     type-IStructure <- (getType name-IStructure)
     type-IStructure <- withReconstructed (return type-IStructure)
     type-IStructure <- normalise type-IStructure

     let (i , mtel , mte , mainPos , lastSort) = buildStruct mainArg type-IStructure
     mainPos <- liftTCMaybe mainPos ("Did not find argument with name " ++ mainArg)
     lastSort <- liftTCMaybe lastSort ("Could not extract level of structure target universe.")

     -- | type of main argument
     let type-mainArg = getFromArg (mainPos .snd)

     -- | Tele optimizations
     -- 1. make hidden, but not inferable variables visible
     let varsOfMain = getVars visible type-mainArg
     let varsToHide = filter (λ i -> not (isUsedInOtherVisibles i mtel mainArg)) varsOfMain
     let mtel = makeVisibleMany visible varsToHide mtel
     -- 2. join Level variables which are near each other
     let dσ-merge , mtel = mergeLevelVars mtel
     let type-mainArg = dσ-merge 0 type-mainArg

     -- | The arguments to call the IStructure with
     let args = insertList (mainPos .fst) (map-Arg {A = Type} {B = ℕ} (∆ zero) (mainPos .snd)) mte
     let args = map-List (map-Arg (λ n -> var n [])) args
     let args = map-List (map-Arg (dσ-merge 1)) args -- merge the 𝔏s

     -- | Tele and variable matchlist for function definition
     let tele = teleFromFullTele mtel
     let varmatches = matchesFromFullTele mtel


     -- printErr ("varsOfMain is: " <> show varsOfMain)
     -- printErr ("tele is: " <> show tele)
     -- printErr ("args is: " <> show args)
     -- printErr ("varmatches is: " <> show varmatches)
     -- printErr ("type-mainArg is: " <> show type-mainArg)

     -- | Skip the first args/tele/matches if we have them in our global tele
     Γ1 <- getContext
     let args = skip-List (length-List Γ1) args
     let tele = skip-List (length-List Γ1) tele
     let varmatches = skip-List (length-List Γ1) varmatches


     -- printErr ("type-mainArg is: " <> show type-mainArg <> "\n\n and checking in context:\n" <> show (Γ1 <> Γ2))
     -- | Computing the result type

     Γ1 <- getContext
     let Γ2 = rev (tele)
     `𝑖` <- inContext (Γ2 <> Γ1)
                      do type-mainArg <- normalise type-mainArg
                         -- curΓ <- getContext
                         -- printErr ("we are in Γ: " <> show curΓ)
                         getLevelOfType type-mainArg



     -- | Generate the return type
     `𝑗` <- sortIntoLevelTerm lastSort
     let `𝑗` = dσ-merge 0 `𝑗`
     let resType = (agda-sort (set (`𝑖` `⊔` `𝑗`)))
     let fullType = makePiType tele resType


     -- printErr ("varsOfMain is: " <> show varsOfMain)
     -- printErr ("tele is: " <> show tele)
     -- printErr ("args is: " <> show args)
     -- printErr ("varmatches is: " <> show varmatches)
     -- printErr ("fullType is: " <> show fullType)
     -- printErr ("resType is: " <> show resType)

     let funArgs = (harg (`𝑖`) ∷ harg `𝑗` ∷ harg (type-mainArg) ∷ varg (lam visible (Abs.abs "MyA" (def name-IStructure args))) ∷ [])
     let fun = (def (quote Structure) funArgs)
     let StrFun = clause tele varmatches fun

     declareDef (varg name-Structure) fullType
     defineFun name-Structure (StrFun ∷ [])

     --------------------------------------------------------------------
     -- | Generate the constructor

     let mtel = makeVisibleAll hidden mtel
     let tele = teleFromFullTele mtel
     let varmatches = matchesFromFullTele mtel

     -- | Skip the first args/tele/matches if we have them in our global tele
     Γ1 <- getContext
     -- let args = skip-List (length-List Γ1) args -- DONT NEED THIS. We did this already above.
     let tele = skip-List (length-List Γ1) tele
     let varmatches = skip-List (length-List Γ1) varmatches

     -- let tele2 = η ("A" , varg type-mainArg) <> η ("Impl" , varg (def name-IStructure args))
     let tele2 = η ("A" , varg type-mainArg) <> η ("Impl" , iarg (def name-IStructure args)) -- CORRECT LINE
     let tele-ctor = tele <> tele2
     let returnType-ctor = liftFrom 0 (liftFrom 0 fun)

     let type-ctor = makePiType tele-ctor returnType-ctor

     -- let varmatches2 = (varg (var 1) ∷ varg (var 0) ∷ [])
     let varmatches2 = (varg (var 1) ∷ iarg (var 0) ∷ []) -- THIS IS THE CORRECT LINE
     let varmatches-ctor = liftPats (liftPats varmatches) <> varmatches2

     -- let term-ctor = con (quote ′_′) ((varg (var 1 []) ∷ varg (var 0 []) ∷ []))
     let term-ctor = con (quote ′_′) ((varg (var 1 []) ∷ iarg (var 0 []) ∷ [])) -- CORRECT LINE
     let clause-ctor = clause tele-ctor varmatches-ctor term-ctor

     -- printErr ("varsOfMain is: " <> show varsOfMain)
     -- printErr ("varmatches is: " <> show varmatches)
     -- printErr ("tele is: " <> show tele)
     -- printErr ("tele-ctor is: " <> show tele-ctor)
     -- printErr ("term-ctor is: " <> show term-ctor)
     -- printErr ("type-ctor is: " <> show type-ctor)
     -- printErr ("varmatches-ctor is: " <> show varmatches-ctor)


     declareDef (varg name-ctor) type-ctor
     defineFun name-ctor (clause-ctor ∷ [])

     -- declareDef (varg name-ctor) (``𝟙``)
     -- defineFun name-ctor (clause [] [] (`tt`) ∷ [])

     return tt




-- open import Verification.Conventions.Category.Base

private
  record IFunctor (X : 𝒰 𝑖) (Y : 𝒰 𝑗) (F : X -> Y) : 𝒰 (𝑖 ､ 𝑗) where
  module _ (A : 𝒰 𝑖) (B : 𝒰 𝑗) (C : 𝒰 𝑖) where
    -- record IMap (f : A -> B) : 𝒰₀ where
    -- unquoteDecl Map map = #struct "?" (quote IMap) "f" Map map

    record IMapi (f : A -> B) (g : A -> B) (p : f ≡ g) : 𝒰₀ where
    unquoteDecl Mapi mapi = #struct "?" (quote IMapi) "p" Mapi mapi

-- Good tests:
  unquoteDecl Functor functor = #struct "?" (quote IFunctor) "F" Functor functor
  unquoteDecl Ring ring = #struct "?" (quote TestStructure.IRing) "A" Ring ring
unquoteDecl MFun mfun = #struct "?" (quote IFunctor) "F" MFun mfun


-- instance
--   Structure:Impl : ∀{A : 𝒰 𝑖} {P : A -> 𝒰 𝑗} -> ∀{x : Ring 𝑖} -> TestStructure.IRing ⟨ x ⟩
--   Structure:Impl = {!!}



  -- -- unquoteDecl MCat mcat = #struct (quote ICategory) "X" MCat mcat

-- unquoteDecl MNat mnat = #struct (quote ITransformation) "α" MNat mnat



-- unquoteDecl Field makeField = #struct (quote IField) "A" Field makeField


-- test123 : (X Y : MCat (ℓ₀ , ℓ₀ , ℓ₀ ,-)) -> (a b c : ⟨ X ⟩) -> (f : Hom a b) -> (g : Hom b c) -> Hom a c
-- test123 X Y a b c f g = f ◆ g


open TestStructure
test : (R : Ring 𝑖) -> ⟨ R ⟩ -> ⟨ R ⟩
test R a = a + a

{-
#struct2 : Name -> String -> Name -> Name -> TC 𝟙-𝒰
#struct2 nameI mainArg a b =
  do
     ``𝟙`` <- quoteTC 𝟙-𝒰
     `tt` <- quoteTC tt

     defT <- (getType nameI)
     defT2 <- withReconstructed (return defT)

     -- printErr (show defT2)

     -- res <- withNormalisation true do
     --    -- defI <- withReconstructed (getDefinition nameI)
     --    return tt

     declareDef (varg a) (``𝟙``)
     defineFun a (clause [] [] (`tt`) ∷ [])

     declareDef (varg b) (``𝟙``)
     defineFun b (clause [] [] (`tt`) ∷ [])

     return tt
-}

    -- dothis : ℕ -> ℕ
    -- dothis n = invert n



-- test : ring ≡ tt
-- test = refl



-- Ring : ∀(𝑖 : 𝔏) -> 𝒰 (𝑖 ⁺)
-- Ring 𝑖 = Structure (IRing {𝑖})

-- ring : ∀{A : 𝒰 ℓ}



-- sum3 : {A : Ring 𝑖} -> (a : ⟨ A ⟩) -> ⟨ A ⟩
-- sum3 a = (a + a) + a


-- record IStructure {A : 𝒰 𝑖} (P : A -> 𝒰 𝑗) (Q : 𝒰 𝑘) : 𝒰 (𝑖 ⊔ 𝑗 ⊔ 𝑘) where
--   field _⌘ : (a : A) -> {{p : P a}} -> Q
--   infixr 200 _⌘
-- open IStructure {{...}} public



-- xx2 = quoteTC ()




-- MyStruct-def : TC Definition
-- MyStruct-def =
--   do n <- freshName "MyStruct"
--      a1n <- freshName "arg1"
--      let a1 = arg (arg-info visible relevant) a1n
--      let myrec = record-type n (a1 ∷ [])
--      return myrec

-- abc = quoteTC `𝟙`





-- makeMyStruct : (st-name : Name) -> TC `𝟙`
-- makeMyStruct st-name = do
--   defineFun (varg )


-- unquoteDecl x = makeMyStruct x



