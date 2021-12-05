
module Verification.Core.Data.SourceCode.Variant.HaskellLike.Definition where

open import Verification.Conventions hiding (ℕ ; lookup)
open import Verification.Core.Data.FinR.Definition
open import Verification.Core.Data.Nat.Definition
open import Verification.Core.Data.AllOf.Sum
open import Verification.Core.Data.Universe.Everything
open import Verification.Core.Data.List.Variant.Unary.Definition
open import Verification.Core.Data.List.Variant.Unary.Instance.Traversable
open import Verification.Core.Category.Std.Functor.Definition
open import Verification.Core.Algebra.Monoid.Definition
open import Verification.Core.Algebra.Monoid.Free
open import Verification.Core.Order.Preorder
-- open import Verification.Core.Data.SourceCode.Variant.Tokenized.Definition

{-# FOREIGN GHC import Hata.Runtime.Core.Data.SourceCode.Variant.HaskellLike.Definition #-}


----------------------------------------------------------
-- Haskell version

data HaskellLikeSourceCode~ (X : 𝒰₀) : 𝒰₀ where
  var : Text -> HaskellLikeSourceCode~ X
  hole : X -> HaskellLikeSourceCode~ X
  newline : ℕ -> HaskellLikeSourceCode~ X
  horizontal : List (ℕ + HaskellLikeSourceCode~ X) -> HaskellLikeSourceCode~ X
  vertical  : ℕ -> List (HaskellLikeSourceCode~ X) -> HaskellLikeSourceCode~ X

{-# COMPILE GHC HaskellLikeSourceCode~ = data HaskellLikeSourceCode (Var | Hole | NewLine | Horizontal | Vertical) #-}

postulate
  parseHaskellLikeSourceCode~ : Text -> Text +-𝒰 HaskellLikeSourceCode~ Text

{-# COMPILE GHC parseHaskellLikeSourceCode~ = parseHaskellLikeSourceCode #-}



----------------------------------------------------------
-- Source with annotations

data HaskellLikeSourceCode (X : 𝒰₀) : 𝒰₀ where
  var : Text -> HaskellLikeSourceCode X
  hole : X -> HaskellLikeSourceCode X
  newline : ℕ -> HaskellLikeSourceCode X
  horizontal : Vec (ℕ +-𝒰 HaskellLikeSourceCode X) n -> HaskellLikeSourceCode X
  vertical  : ℕ -> Vec (HaskellLikeSourceCode X) n -> HaskellLikeSourceCode X

module _ (X : 𝒰₀) where
  macro HsCode = #structureOn (HaskellLikeSourceCode X)


module _ {X : 𝒰₀} where
  data HaskellLikeSourceCodeLoc : (γ : HaskellLikeSourceCode X) -> 𝒰₀ where
    hole : {x : X} -> HaskellLikeSourceCodeLoc (hole x)
    horizontal : ∀{x} {vs : Vec (ℕ +-𝒰 HaskellLikeSourceCode X) n} -> (i : Fin-R n)
                 -> lookup i vs ≣ right x
                 -> HaskellLikeSourceCodeLoc (x)
                 -> HaskellLikeSourceCodeLoc (horizontal vs)
    vertical : ∀{n x} {vs : Vec (HaskellLikeSourceCode X) n} -> (i : Fin-R n) -> lookup i vs ≣ x
                 -> HaskellLikeSourceCodeLoc (x)
                 -> HaskellLikeSourceCodeLoc (vertical n vs)

  module _ (γ : HsCode X) where
    macro
      HsLoc = #structureOn (HaskellLikeSourceCodeLoc γ)

  instance
    isSetoid:HsLoc : ∀{γ} -> isSetoid (HsLoc γ)
    isSetoid:HsLoc = isSetoid:byId

  module _ {γ : HsCode X} where
    data _≤-HsLoc_ : (a b : HsLoc γ) -> 𝒰₀ where
      reflexive-⧜ : ∀{a} -> a ≤-HsLoc a

  instance
    isPreorder:HsLoc : ∀{γ} -> isPreorder _ (HsLoc γ)
    isPreorder:HsLoc = record { _≤_ = _≤-HsLoc_ ; reflexive = {!!} ; _⟡_ = {!!} ; transp-≤ = {!!} }

----------------------------------------------------------
-- Annotations

{-
record AnnotationSpan (A : 𝒰₀) (n : ℕ) : 𝒰₀ where
  field annotation : A
  field fstSpan : ℕ
  field sndSpan : ℕ
  field fstSpanP : fstSpan ≤ sndSpan
  field sndSpanP : sndSpan ≤ n

data LinearAnnotation (A : 𝒰₀) : (num : ℕ) -> (n : ℕ) -> (as : List A) -> 𝒰₀ where
  start : LinearAnnotation A 0 0 []
  begin : ∀{as a} -> LinearAnnotation A m n as -> LinearAnnotation A m n (a ∷ as)
  end : ∀{as} -> (a : A) -> LinearAnnotation A m n (a ∷ as) -> LinearAnnotation A (suc m) n as
  step : ∀{as} -> LinearAnnotation A m n (as) -> LinearAnnotation A m (suc n) as


record AnnotatedPlanarLine (A : 𝒰₀) : 𝒰₀ where
  constructor annline
  field annSize : ℕ
  field lineSize : ℕ
  field tokens : Vec (Text) lineSize
  field annotations : LinearAnnotation A annSize lineSize []

open AnnotatedPlanarLine public

record AnnotatedPlanarText (A : 𝒰₀) : 𝒰₀ where
  constructor anntext
  field annSize : ℕ
  field textSize : ℕ
  field lines : Vec (AnnotatedPlanarLine A) textSize
  field annotations : LinearAnnotation A annSize textSize []

open AnnotatedPlanarText public

module _ {A : 𝒰₀} {{_ : IShow A}} where
  printAnnotatedLine : AnnotatedPlanarLine A -> Text
  printAnnotatedLine (annline m n tok ann) = printAllAnn ann tok
    where

      fnomark : ∀{as m n} -> LinearAnnotation A m n as -> Vec Text n -> Vec (Text ×-𝒰 Bool) n
      fnomark start text = ⦋⦌
      fnomark (begin ann) text = fnomark ann text
      fnomark (end a ann) text = fnomark ann text
      fnomark (step ann) (x ∷ text) = (x , false) ∷ (fnomark ann text)

      fmark : ∀{as m n} -> ℕ -> LinearAnnotation A m n as -> Vec Text n -> Vec (Text ×-𝒰 Bool) n
      fmark sta start text = ⦋⦌
      fmark zero (begin ann) text = fnomark ann text
      fmark (suc sta) (begin ann) text = fmark sta ann text
      fmark sta (end a ann) text = fmark (suc sta) ann text
      fmark sta (step ann) (x ∷ text) = (x , true) ∷ (fmark sta ann text)

      f : ∀{as m n} -> (cur : (Fin-R m)) -> LinearAnnotation A m n as -> Vec Text n -> A ×-𝒰 Vec (Text ×-𝒰 Bool) n
      f cur (begin ann) text = f cur ann text
      f zero (end a ann) text = a , fmark 0 ann text
      f (suc cur) (end a ann) text = f cur ann text
      f cur (step ann) (t ∷ text) =
        let a , res = f cur ann text
        in a , ((t , false) ∷ res)

      printVec : ∀{n} -> Vec (Text ×-𝒰 Bool) n -> Text ×-𝒰 Text
      printVec ⦋⦌ = "> " , "| "
      printVec ((t , b) ∷ xs) = let (x , y) = printVec xs in (t <> " " <> x) , (makeUnderline (getChar b) t) <> " " <> y
        where
          open import Agda.Builtin.Char
          makeUnderline : Char -> Text -> Text
          makeUnderline a text = primStringFromList $ map-List (const a) $ primStringToList text

          getChar : Bool -> Char
          getChar true = '~'
          getChar false = ' '

      printFullAnn : ∀{as m n} -> (cur : (Fin-R m)) -> LinearAnnotation A m n as -> Vec Text n -> Text
      printFullAnn cur ann text =
        let a , vec = f cur ann text
            pvec1 , pvec2 = printVec vec
            rest = "| " <> show a
        in pvec1 <> "\n" <> pvec2 <> "\n" <> rest <> "\n"

      printAllAnn : ∀{as m n} -> LinearAnnotation A m n as -> Vec Text n -> Text
      printAllAnn ann text = printLines $ map-List (\cur -> printFullAnn cur ann text) $ getAllFins
        where
          ii : ∀{m} -> Fin-R m -> Fin-R (suc m)
          ii zero = zero
          ii (suc a) = suc (ii a)

          getAllFins : ∀{m} -> List (Fin-R m)
          getAllFins {zero} = []
          getAllFins {suc m} = zero ∷ map-List ii (getAllFins {m})

          printLines : List Text -> Text
          printLines ⦋⦌ = ""
          printLines (x ∷ txt) = x <> "\n" <> printLines txt
-}



instance
  IShow:HaskellLikeSourceCode : ∀{X} -> {{_ : IShow X}} -> IShow (HaskellLikeSourceCode X)
  IShow:HaskellLikeSourceCode {X} = record { show = f }
    where
      mutual
        space : ℕ -> Text
        space zero = ""
        space (suc n) = " " <> space n

        mkNewline : ℕ -> Text
        mkNewline zero = ""
        mkNewline (suc n) = "\n" <> mkNewline n

        verts : Vec (ℕ + HaskellLikeSourceCode X) n -> Text
        verts [] = ""
        verts (left n ∷ xs) = "\n" <> space n <> verts xs
        verts (just x ∷ xs) = f x <> " " <> verts xs

        horizs : ℕ -> Vec (HaskellLikeSourceCode X) n -> Text
        horizs n [] = ""
        horizs n (x ∷ xs) = "\n" <> space n <> f x <> horizs n xs

        f : HaskellLikeSourceCode X → Text
        f (var x) = x
        f (hole x) = "{" <> show x <> "}"
        f (newline x) = mkNewline x
        f (horizontal x) = "(" <> verts x <> ")"
        f (vertical n xs) = "where" <> horizs n xs


-------------------------
-- going from haskell to native



instance
  hasInclusion:HaskellLikeSourceCode,HaskellLikeSourceCode : ∀{X} -> hasInclusion (HaskellLikeSourceCode~ X) (HaskellLikeSourceCode X)
  hasInclusion:HaskellLikeSourceCode,HaskellLikeSourceCode {X} = inclusion f
    where
      mutual
        fs : (xs : List (ℕ + HaskellLikeSourceCode~ X)) → Vec (ℕ + HaskellLikeSourceCode X) (length xs)
        fs [] = []
        fs (left x ∷ xs) = left x ∷ fs xs
        fs (right x ∷ xs) = right (f x) ∷ fs xs

        gs : (xs : List (HaskellLikeSourceCode~ X)) → Vec (HaskellLikeSourceCode X) (length xs)
        gs [] = []
        gs (x ∷ xs) = f x ∷ gs xs

        f : HaskellLikeSourceCode~ X → HaskellLikeSourceCode X
        f (var x) = var x
        f (hole x) = hole x
        f (newline x) = newline x
        f (horizontal xs) = horizontal (fs xs)
        f (vertical x xs) = vertical x (gs xs)


parseHaskellLikeSourceCode : Text -> Text + HaskellLikeSourceCode Text
parseHaskellLikeSourceCode = mapRight ι ∘ parseHaskellLikeSourceCode~






