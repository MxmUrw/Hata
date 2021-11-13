
module Verification.Core.Data.Tree.Variant.Syntax.Instance.Infer where

open import Verification.Conventions hiding (lookup ; ℕ)

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

module _ {A B : 𝒰 𝑖} {F : 𝒰 𝑖 -> 𝒰 𝑖} {{_ : isFunctor (𝐔𝐧𝐢𝐯 𝑖) (𝐔𝐧𝐢𝐯 𝑖) F}} where
  _<$>_ : (A -> B) -> F A -> F B
  _<$>_ f x = {!!}



data SyntaxTreeToken : 𝒰₀ where
  binder : SyntaxTreeToken

tokenSize-SyntaxTreeToken : SyntaxTreeToken -> ♮ℕ
tokenSize-SyntaxTreeToken binder = 2

tokenName-SyntaxTreeToken : SyntaxTreeToken -> Text
tokenName-SyntaxTreeToken binder = "↦"

toTokenTreeData : SyntaxTreeData -> TokenTreeData
toTokenTreeData 𝒹 = record
  { TokenType = SyntaxTreeToken + (TokenType 𝒹)
  ; tokenSize = either tokenSize-SyntaxTreeToken (λ xs -> map-List (const tt) (tokenSize 𝒹 xs))
  ; tokenName = either tokenName-SyntaxTreeToken (tokenName 𝒹)
  ; tokenList = left binder ∷ map-List right (tokenList 𝒹)
  }

private δ = toTokenTreeData

module _ {𝒹 : SyntaxTreeData} where
  -----------------------------------------
  -- printing of the syntax tree
  mutual

    printᵘ-SyntaxTreeBindingWithHole : ∀ {A} {Γ} {n} -> SyntaxTreeBindingWithHole 𝒹 A Γ n -> TokenTree (δ 𝒹) (∑ A)
    printᵘ-SyntaxTreeBindingWithHole (skipBinding x) = printᵘ-SyntaxTree' _ _ x -- hole (_ , x)
    printᵘ-SyntaxTreeBindingWithHole (incl x) = printᵘ-SyntaxTreeBinding x

    printᵘ-SyntaxTreeBinding : ∀ {A} {Γ} {n} -> SyntaxTreeBinding 𝒹 A Γ n -> TokenTree (δ 𝒹) (∑ A)
    printᵘ-SyntaxTreeBinding (incl x) = printᵘ-SyntaxTree' _ _ x
    -- printᵘ-SyntaxTreeBinding (hole x rest) = {!!} -- hole (_ , x)
    printᵘ-SyntaxTreeBinding (bind name x) = node (left binder) ((var name) ∷ (printᵘ-SyntaxTreeBinding x) ∷ [])


    printᵘ-SyntaxTrees : ∀ {A} {Γ} {n} -> DList (SyntaxTreeBindingWithHole 𝒹 (ix A) Γ) (n)
                                          -> ConstDList (TokenTreeᵘ (δ 𝒹) (⨆ᵘ A)) (map-List (const tt) n)
    printᵘ-SyntaxTrees [] = []
    printᵘ-SyntaxTrees (x ∷ xs) = printᵘ-SyntaxTreeBindingWithHole x ∷ (printᵘ-SyntaxTrees xs)

    -- NOTE: we need to write the induction without the ∑ on SyntaxTree,
    --       because with it, the termination checker does not see that
    --       the recursion terminates. Hence this implementation version with "'"
    printᵘ-SyntaxTree' : ∀ A i -> (SyntaxTreeᵈ 𝒹 A) i -> TokenTree (δ 𝒹) (∑ A)
    printᵘ-SyntaxTree' A i (hole x) = hole (i , x)
    printᵘ-SyntaxTree' A i (var name x) = var name
    printᵘ-SyntaxTree' A i (node t x) = node (right t) (printᵘ-SyntaxTrees x)
    printᵘ-SyntaxTree' A i (annotation a x) = annotation a (printᵘ-SyntaxTree' A i x)

  printᵘ-SyntaxTree : ∀ A -> ⨆ (SyntaxTree 𝒹 A) -> TokenTree (δ 𝒹) (⨆ A)
  printᵘ-SyntaxTree A (i , x) = printᵘ-SyntaxTree' (ix A) i x

  print-SyntaxTree : 大MonadHom (_ , SyntaxTree 𝒹) (_ , TokenTree (δ 𝒹))
  print-SyntaxTree = record { fst = ⨆ ; snd = printᵘ-SyntaxTree since {!!} }


  -----------------------------------------
  -- Parsing from a token tree

  mutual
    parseᵘ-SyntaxTreeBinding : ∀ {A} {Γ} {n}
                           -> (TokenTreeᵘ (δ 𝒹) (A))
                           -> Maybe (SyntaxTreeBinding 𝒹 (ix (写 (TokenTree (δ 𝒹) A))) Γ n)
    parseᵘ-SyntaxTreeBinding {Γ = Γ} {n = ⦋⦌} t = just $ incl (parseᵘ-SyntaxTree' Γ t)

    parseᵘ-SyntaxTreeBinding {Γ = Γ} {n = tt ∷ n} (node (left binder) (var name ∷ (t ∷ []))) = bind name <$> (parseᵘ-SyntaxTreeBinding t)
    parseᵘ-SyntaxTreeBinding {Γ = Γ} {n = tt ∷ n} other@(t) = {!!} -- hole (annotation "Expected binder here." other)

    parseᵘ-SyntaxTrees : ∀ {A} {Γ} {n}
                           -> ConstDList (TokenTreeᵘ (δ 𝒹) (A)) (map-List (const tt) n)
                           -> DList (SyntaxTreeBindingWithHole 𝒹 (ix (写 (TokenTree (δ 𝒹) A))) Γ) (n)
    parseᵘ-SyntaxTrees {n = ⦋⦌} [] = []
    parseᵘ-SyntaxTrees {n = _ ∷ _} (x ∷ xs) =
      either (const (skipBinding (hole x))) incl (parseᵘ-SyntaxTreeBinding x)
      ∷ parseᵘ-SyntaxTrees xs


    parseᵘ-SyntaxTree' : ∀ {A} -> (Γ : 人List Text) -> TokenTree (δ 𝒹) A -> (ix (SyntaxTree 𝒹 (写 (TokenTree (δ 𝒹) A))) Γ)
    parseᵘ-SyntaxTree' Γ (hole x) = hole (hole x)
    parseᵘ-SyntaxTree' Γ (var x) = case find-first-∍ Γ x of
                                           (λ p -> hole (annotation ("The variable " <> x <> " is not in scope") (var x)))
                                           (λ Γ∍x → var x Γ∍x)
    parseᵘ-SyntaxTree' Γ (node (left binder) x) = hole (annotation "No variable binding allowed here." ((node (left binder) x)))
    parseᵘ-SyntaxTree' Γ (node (just t) x) = node t (parseᵘ-SyntaxTrees x)
    parseᵘ-SyntaxTree' Γ (annotation a x) = annotation a (parseᵘ-SyntaxTree' Γ x)

  parseᵘ-SyntaxTree : ∀ A -> TokenTree (δ 𝒹) A -> (⨆ (SyntaxTree 𝒹 (写 (TokenTree (δ 𝒹) A))))
  parseᵘ-SyntaxTree A t = _ , parseᵘ-SyntaxTree' ◌ t


  -----------------------------------------
  -- This gives us an inference morphism

  isInferHom:print-SyntaxTree : isInferHom print-SyntaxTree
  isInferHom:print-SyntaxTree = record
    { inferF = 写
    ; infer = parseᵘ-SyntaxTree since {!!}
    ; eval-infer = {!!}
    }

  infer-SyntaxTree : SyntaxTreeInfer 𝒹 ⟶ TokenTreeInfer (δ 𝒹)
  infer-SyntaxTree = subcathom print-SyntaxTree isInferHom:print-SyntaxTree



