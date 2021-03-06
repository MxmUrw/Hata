
module Verification.Core.Data.Tree.Variant.Syntax.Instance.Infer where

open import Verification.Conventions hiding (โ)

open import Verification.Core.Set.AllOf.Setoid
open import Verification.Core.Data.AllOf.Collection.Basics
open import Verification.Core.Data.AllOf.Collection.TermTools
open import Verification.Core.Category.Std.AllOf.Collection.Basics
open import Verification.Core.Category.Std.AllOf.Collection.Limits
open import Verification.Core.Category.Std.AllOf.Collection.Monads

open import Verification.Core.Theory.Std.Inference.Definition
open import Verification.Core.Theory.Std.Inference.Task

open import Verification.Core.Data.Tree.Variant.Syntax.Data
open import Verification.Core.Data.Tree.Variant.Syntax.Definition
open import Verification.Core.Data.Tree.Variant.Syntax.Instance.Monad

open import Verification.Core.Data.Tree.Variant.Token.Data
open import Verification.Core.Data.Tree.Variant.Token.Definition
open import Verification.Core.Data.Tree.Variant.Token.Instance.Monad

module _ {A B : ๐ฐ ๐} {F : ๐ฐ ๐ -> ๐ฐ ๐} {{_ : isFunctor (๐๐ง๐ข๐ฏ ๐) (๐๐ง๐ข๐ฏ ๐) F}} where
  _<$>_ : (A -> B) -> F A -> F B
  _<$>_ f x = {!!}



data SyntaxTreeToken : ๐ฐโ where
  binder : SyntaxTreeToken

tokenSize-SyntaxTreeToken : SyntaxTreeToken -> โฎโ
tokenSize-SyntaxTreeToken binder = 2

tokenName-SyntaxTreeToken : SyntaxTreeToken -> Text
tokenName-SyntaxTreeToken binder = "โฆ"

toTokenTreeData : SyntaxTreeData -> TokenTreeData
toTokenTreeData ๐น = record
  { TokenType = SyntaxTreeToken + (TokenType ๐น)
  ; tokenSize = either tokenSize-SyntaxTreeToken (ฮป xs -> map-List (const tt) (tokenSize ๐น xs))
  ; tokenName = either tokenName-SyntaxTreeToken (tokenName ๐น)
  ; tokenList = left binder โท map-List right (tokenList ๐น)
  }

private ฮด = toTokenTreeData

module _ {๐น : SyntaxTreeData} where
  -----------------------------------------
  -- printing of the syntax tree
  mutual

    printแต-SyntaxTreeBindingWithHole : โ {A} {ฮ} {n} -> SyntaxTreeBindingWithHole ๐น A ฮ n -> TokenTree (ฮด ๐น) (โ A)
    printแต-SyntaxTreeBindingWithHole (skipBinding x) = printแต-SyntaxTree' _ _ x -- hole (_ , x)
    printแต-SyntaxTreeBindingWithHole (incl x) = printแต-SyntaxTreeBinding x

    printแต-SyntaxTreeBinding : โ {A} {ฮ} {n} -> SyntaxTreeBinding ๐น A ฮ n -> TokenTree (ฮด ๐น) (โ A)
    printแต-SyntaxTreeBinding (incl x) = printแต-SyntaxTree' _ _ x
    -- printแต-SyntaxTreeBinding (hole x rest) = {!!} -- hole (_ , x)
    printแต-SyntaxTreeBinding (bind name x) = node (left binder) ((var name) โท (printแต-SyntaxTreeBinding x) โท [])


    printแต-SyntaxTrees : โ {A} {ฮ} {n} -> Listแดฐ (SyntaxTreeBindingWithHole ๐น (ix A) ฮ) (n)
                                          -> ConstListแดฐ (TokenTreeแต (ฮด ๐น) (โจแต A)) (map-List (const tt) n)
    printแต-SyntaxTrees [] = []
    printแต-SyntaxTrees (x โท xs) = printแต-SyntaxTreeBindingWithHole x โท (printแต-SyntaxTrees xs)

    -- NOTE: we need to write the induction without the โ on SyntaxTree,
    --       because with it, the termination checker does not see that
    --       the recursion terminates. Hence this implementation version with "'"
    printแต-SyntaxTree' : โ A i -> (SyntaxTreeแต ๐น A) i -> TokenTree (ฮด ๐น) (โ A)
    printแต-SyntaxTree' A i (hole x) = hole (i , x)
    printแต-SyntaxTree' A i (var name x) = var name
    printแต-SyntaxTree' A i (node t x) = node (right t) (printแต-SyntaxTrees x)
    printแต-SyntaxTree' A i (annotation a x) = annotation a (printแต-SyntaxTree' A i x)

  printแต-SyntaxTree : โ A -> โจ (SyntaxTree ๐น A) -> TokenTree (ฮด ๐น) (โจ A)
  printแต-SyntaxTree A (i , x) = printแต-SyntaxTree' (ix A) i x

  print-SyntaxTree : ๅคงMonadHom (_ , SyntaxTree ๐น) (_ , TokenTree (ฮด ๐น))
  print-SyntaxTree = record { fst = โจ ; snd = printแต-SyntaxTree since {!!} }


  -----------------------------------------
  -- Parsing from a token tree

  mutual
    parseแต-SyntaxTreeBinding : โ {A} {ฮ} {n}
                           -> (TokenTreeแต (ฮด ๐น) (A))
                           -> Maybe (SyntaxTreeBinding ๐น (ix (ๅ (TokenTree (ฮด ๐น) A))) ฮ n)
    parseแต-SyntaxTreeBinding {ฮ = ฮ} {n = โฆโฆ} t = just $ incl (parseแต-SyntaxTree' ฮ t)

    parseแต-SyntaxTreeBinding {ฮ = ฮ} {n = tt โท n} (node (left binder) (var name โท (t โท []))) = bind name <$> (parseแต-SyntaxTreeBinding t)
    parseแต-SyntaxTreeBinding {ฮ = ฮ} {n = tt โท n} other@(t) = {!!} -- hole (annotation "Expected binder here." other)

    parseแต-SyntaxTrees : โ {A} {ฮ} {n}
                           -> ConstListแดฐ (TokenTreeแต (ฮด ๐น) (A)) (map-List (const tt) n)
                           -> Listแดฐ (SyntaxTreeBindingWithHole ๐น (ix (ๅ (TokenTree (ฮด ๐น) A))) ฮ) (n)
    parseแต-SyntaxTrees {n = โฆโฆ} [] = []
    parseแต-SyntaxTrees {n = _ โท _} (x โท xs) =
      either (const (skipBinding (hole x))) incl (parseแต-SyntaxTreeBinding x)
      โท parseแต-SyntaxTrees xs


    parseแต-SyntaxTree' : โ {A} -> (ฮ : โList Text) -> TokenTree (ฮด ๐น) A -> (ix (SyntaxTree ๐น (ๅ (TokenTree (ฮด ๐น) A))) ฮ)
    parseแต-SyntaxTree' ฮ (hole x) = hole (hole x)
    parseแต-SyntaxTree' ฮ (var x) = case find-first-โ ฮ x of
                                           (ฮป p -> hole (annotation ("The variable " <> x <> " is not in scope") (var x)))
                                           (ฮป ฮโx โ var x ฮโx)
    parseแต-SyntaxTree' ฮ (node (left binder) x) = hole (annotation "No variable binding allowed here." ((node (left binder) x)))
    parseแต-SyntaxTree' ฮ (node (just t) x) = node t (parseแต-SyntaxTrees x)
    parseแต-SyntaxTree' ฮ (annotation a x) = annotation a (parseแต-SyntaxTree' ฮ x)

  parseแต-SyntaxTree : โ A -> TokenTree (ฮด ๐น) A -> (โจ (SyntaxTree ๐น (ๅ (TokenTree (ฮด ๐น) A))))
  parseแต-SyntaxTree A t = _ , parseแต-SyntaxTree' โ t


  -----------------------------------------
  -- This gives us an inference morphism

  isInferHom:print-SyntaxTree : isInferHom print-SyntaxTree
  isInferHom:print-SyntaxTree = record
    { inferF = ๅ
    ; infer = parseแต-SyntaxTree since {!!}
    ; eval-infer = {!!}
    }

  infer-SyntaxTree : SyntaxTreeInfer ๐น โถ TokenTreeInfer (ฮด ๐น)
  infer-SyntaxTree = subcathom print-SyntaxTree isInferHom:print-SyntaxTree



