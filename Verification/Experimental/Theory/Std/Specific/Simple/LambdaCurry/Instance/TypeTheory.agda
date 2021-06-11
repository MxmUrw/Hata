
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

private
  instance
    λCurry : isTypeTheory _ ′ Curry.Statement ′
    isTypeTheory.Termᵘ λCurry = Curry.Term-λ
    isTypeTheory.isSetoid:Term λCurry = it
    isTypeTheory._∶_ λCurry = λ t (_ , Γ ⊢ τ) -> t ∶ Γ ⊢ τ
    isTypeTheory.preserveType λCurry (incl refl-StrId) t = t


macro
  𝟙 : ∀{𝑖} -> SomeStructure
  𝟙 {𝑖} = #structureOn (⊤-𝒰 {𝑖})

private
  f : ⊤-𝒰 ⟶ TypeTheory _
  f = incl (const ′ Curry.Statement ′)

zeta : Fiber _ ⊤-𝒰
zeta = ⟨ f *! ⟩ (𝐓𝐓Fib _)

private macro
  p = instance[ "" , 𝑖 / 3 ] (𝐅𝐚𝐦 (𝐐𝐮𝐞𝐬𝐭 (𝑖 ⌄ 0 ⋯ 1)) (𝑖 ⌄ 2) -> 𝐓𝐲𝐩𝐞 _) ◀

trivialF : ∀{𝑖} -> ∀{A} -> Fiber (p {𝑖}) A
trivialF {A = A} = (A since family (λ _ -> TRIVIAL))
           since record { isSectionFiber = refl }

module _ {A : 𝒰 _} B (π : A -> p {𝑖} B) where
  Solution : 𝒰 _
  Solution = ⟨ incl π *! ⟩ ′ B ′ ⟶ trivialF

record SolvedTypeTheoryClass 𝑖 : 𝒰 (𝑖 ⁺ ⁺) where
  field Param : 𝒰 _
  field theory : Param -> TypeTheory 𝑖
  field solution : Solution (𝐓𝐓Fam 𝑖) theory

open SolvedTypeTheoryClass public

checkClass : (𝓣 : SolvedTypeTheoryClass 𝑖) -> (p : Param 𝓣) -> (t : Term {{of theory 𝓣 p}}) -> (τ : ⟨ theory 𝓣 p ⟩) -> isDecidable (_∶_ {{of theory 𝓣 p}} t τ)
checkClass 𝓣 p t =
  let X = map-■ {{of ⟨ ⟨ ⟨ solution 𝓣 ⟩ ⟩ ⟩}}
  in {!!}


-- (𝐓𝐓Fam _ since record { isSectionFiber = refl })


  -- (obj (𝐓𝐓Fam _))

  -- g : ⊤-𝒰 ⟶ 𝐐𝐮𝐞𝐬𝐭 _
  -- g = {!!}







