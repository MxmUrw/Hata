
module Verification.Core.Theory.Std.Specific.Simple.LambdaCurry.Instance.TypeTheory where

open import Verification.Core.Conventions
open import Verification.Core.Set.Setoid
open import Verification.Core.Set.Discrete
open import Verification.Core.Set.Decidable
open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Data.Universe.Instance.Category
-- open import Verification.Core.Theory.Std.Presentation.Signature.SingleSorted.Definition
open import Verification.Core.Theory.Std.Specific.Simple.LambdaCurry.Definition as Curry
-- open import Verification.Core.Theory.Std.Specific.Simple.LambdaCurry.Definition using (_∶_⊢_)
open import Verification.Core.Theory.Std.Generic.TypeTheory.Definition
open import Verification.Core.Computation.Question.Definition
open import Verification.Core.Computation.Question.Specific.Small

open import Verification.Core.Category.Std.Fibration.BaseChange.Definition
open import Verification.Core.Category.Std.Fibration.Definition
open import Verification.Core.Category.Std.Fibration.Instance.BaseChange

open import Verification.Core.Category.Std.Limit.Specific.Pullback
-- open import Verification.Core.Category.Std.Fibration.Specific.Fam.Definition
open import Verification.Core.Data.Universe.Everything

open import Verification.Core.Theory.Std.Generic.ProgrammingLanguage.Definition
open import Verification.Core.Category.Std.Graph.Definition


private
  instance
    isGraph:CurryTerm : isGraph (Curry.Term-λ 0)
    isGraph:CurryTerm = graph (const (const 𝟙-𝒰))

  instance
    λCurry : isTypeTheory (ℓ₀ , ℓ₀ , ℓ₀) Curry.Statement
    isTypeTheory.Termᵘ λCurry = Curry.Term-λ 0
    isTypeTheory.isSetoid:Term λCurry = {!!}
    isTypeTheory._∶_ λCurry = {!!} -- λ t (_ , Γ ⊢ τ) -> t ∶ Γ ⊢ τ
    isTypeTheory.preserveType λCurry = {!!} -- (refl-StrId) t = t

  instance
    isLanguage:Curry : isLanguage (ℓ₀ , ℓ₀ , ℓ₀) (Curry.Statement)
    isLanguage:Curry =
      language
        (Curry.Term-λ 0)
        {!!} -- (λ t (_ , Γ ⊢ τ) -> t ∶ Γ ⊢ τ)
        {!!}


macro
  𝟙 : ∀{𝑖} -> SomeStructure
  𝟙 {𝑖} = #structureOn (⊤-𝒰 {𝑖})

private
  f : ⊤-𝒰 ⟶ TypeTheory _
  f = (const ′ Curry.Statement ′)

zeta : Fiber _ ⊤-𝒰
zeta = ⟨ f *! ⟩ (𝐓𝐓Fib _)

-- private macro
--   p = instance[ "" , 𝑖 / 3 ] (𝐅𝐚𝐦 (𝐐𝐮𝐞𝐬𝐭 (𝑖 ⌄ 0 ⋯ 1)) (𝑖 ⌄ 2) -> 𝐓𝐲𝐩𝐞 _) ◀

λC : LanguageClass _
λC = languageClass "curry" ⊤-𝒰 (const ′ Curry.Statement ′)

instance
  isImplemented:λC : isImplemented λC
  isImplemented:λC = {!!} -- isimplemented {!!}







-- (𝐓𝐓Fam _ since record { isSectionFiber = refl })


  -- (obj (𝐓𝐓Fam _))

  -- g : ⊤-𝒰 ⟶ 𝐐𝐮𝐞𝐬𝐭 _
  -- g = {!!}







