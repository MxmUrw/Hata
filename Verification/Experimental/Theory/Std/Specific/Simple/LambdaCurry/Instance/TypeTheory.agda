
module Verification.Experimental.Theory.Std.Specific.Simple.LambdaCurry.Instance.TypeTheory where

open import Verification.Experimental.Conventions
open import Verification.Experimental.Set.Setoid
open import Verification.Experimental.Set.Discrete
open import Verification.Experimental.Set.Decidable
open import Verification.Experimental.Category.Std.Category.Definition
open import Verification.Experimental.Data.Universe.Instance.Category
-- open import Verification.Experimental.Theory.Std.Presentation.Signature.SingleSorted.Definition
open import Verification.Experimental.Theory.Std.Specific.Simple.LambdaCurry.Definition as Curry
open import Verification.Experimental.Theory.Std.Specific.Simple.LambdaCurry.Definition using (_∶_⊢_)
open import Verification.Experimental.Theory.Std.TypeTheory.Definition
open import Verification.Experimental.Computation.Question.Definition
open import Verification.Experimental.Computation.Question.Specific.Small

open import Verification.Experimental.Category.Std.Fibration.BaseChange.Definition
open import Verification.Experimental.Category.Std.Fibration.Definition
open import Verification.Experimental.Category.Std.Fibration.Instance.BaseChange

open import Verification.Experimental.Category.Std.Limit.Specific.Pullback
open import Verification.Experimental.Category.Std.Fibration.Specific.Fam.Definition
open import Verification.Experimental.Data.Universe.Everything

open import Verification.Experimental.Theory.Std.ProgrammingLanguage.Definition
open import Verification.Experimental.Category.Std.Graph.Definition


private
  instance
    isGraph:CurryTerm : isGraph Curry.Term-λ
    isGraph:CurryTerm = graph (const (const 𝟙-𝒰))

  instance
    λCurry : isTypeTheory _ Curry.Statement
    isTypeTheory.Termᵘ λCurry = Curry.Term-λ
    isTypeTheory.isSetoid:Term λCurry = it
    isTypeTheory._∶_ λCurry = λ t (_ , Γ ⊢ τ) -> t ∶ Γ ⊢ τ
    isTypeTheory.preserveType λCurry (incl refl-StrId) t = t

  instance
    isLanguage:Curry : isLanguage _ (Curry.Statement)
    isLanguage:Curry =
      language
        Curry.Term-λ
        (λ t (_ , Γ ⊢ τ) -> t ∶ Γ ⊢ τ)
        {!!}


macro
  𝟙 : ∀{𝑖} -> SomeStructure
  𝟙 {𝑖} = #structureOn (⊤-𝒰 {𝑖})

private
  f : ⊤-𝒰 ⟶ TypeTheory _
  f = incl (const ′ Curry.Statement ′)

zeta : Fiber _ ⊤-𝒰
zeta = ⟨ f *! ⟩ (𝐓𝐓Fib _)

-- private macro
--   p = instance[ "" , 𝑖 / 3 ] (𝐅𝐚𝐦 (𝐐𝐮𝐞𝐬𝐭 (𝑖 ⌄ 0 ⋯ 1)) (𝑖 ⌄ 2) -> 𝐓𝐲𝐩𝐞 _) ◀

λC : LanguageClass _
λC = languageClass "curry" ⊤-𝒰 (const ′ Curry.Statement ′)

instance
  isImplemented:λC : isImplemented λC
  isImplemented:λC = isimplemented {!!}


-- (𝐓𝐓Fam _ since record { isSectionFiber = refl })


  -- (obj (𝐓𝐓Fam _))

  -- g : ⊤-𝒰 ⟶ 𝐐𝐮𝐞𝐬𝐭 _
  -- g = {!!}







