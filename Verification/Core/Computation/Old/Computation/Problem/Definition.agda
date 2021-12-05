
module Verification.Core.Theory.Computation.Problem.Definition where

open import Verification.Core.Conventions
open import Verification.Core.Set.Setoid.Definition
open import Verification.Core.Data.Universe.Definition
open import Verification.Core.Data.Universe.Instance.Category
open import Verification.Core.Data.Prop.Everything
open import Verification.Core.Order.WellFounded.Definition
open import Verification.Core.Order.Preorder
open import Verification.Core.Category.Std.Category.Definition


---------------------------------------------------------------
-- Definition of a problem

record isProblem (𝑖 : 𝔏) (A : 𝒰 𝑗) : 𝒰 (𝑖 ⁺ ､ 𝑗) where
  constructor problem
  field Solution : (A -> 𝒰 𝑖)

open isProblem {{...}} public

Problem : (𝑖 : 𝔏 ^ 2) -> 𝒰 _
Problem 𝑖 = 𝒰' (𝑖 ⌄ 0) :& isProblem (𝑖 ⌄ 1)

macro
  𝐏𝐫𝐨𝐛 : ∀ (𝑖 : 𝔏 ^ 2) -> SomeStructure
  𝐏𝐫𝐨𝐛 𝑖 = #structureOn (Problem 𝑖)

mymap : ∀{𝑖 : 𝔏 ^ 2} -> 𝐏𝐫𝐨𝐛 𝑖 -> 𝐏𝐫𝐨𝐛 𝑖
mymap a = a

---------------------------------------------------------------
-- Definition of problem morphisms

module _ (A : 𝐏𝐫𝐨𝐛 (𝑖 , 𝑘)) (B : 𝐏𝐫𝐨𝐛 (𝑗 , 𝑘)) where
  record isDeductive (f : ⟨ A ⟩ -> ⟨ B ⟩) : 𝒰 (𝑖 ､ 𝑘) where
    constructor deductive
    field deduct : Solution {{of A}} ≤ (Solution {{of B}} ∣ f)

  open isDeductive {{...}} public

  Deduction : 𝒰 _
  Deduction = _ :& isDeductive

private
  instance
    id-Problem : ∀{A : Problem 𝑖} -> isDeductive A A id-𝒰
    id-Problem = record
      { deduct = reflexive
      }

  instance
    comp-Problem : ∀{A B C : Problem 𝑖} -> {f : Deduction A B} -> {g : Deduction B C} -> isDeductive A C (⟨ f ⟩ ◆-𝒰 ⟨ g ⟩)
    comp-Problem {f = f} {g = g} = record
      { deduct = deduct {{of f}} ⟡ incl (λ x → ⟨ deduct {{of g}} ⟩ x)
      }

---------------------------------------------------------------
-- The category of problems

instance
  isCategory:𝐏𝐫𝐨𝐛 : isCategory _ (𝐏𝐫𝐨𝐛 𝑖)
  isCategory:𝐏𝐫𝐨𝐛 =
    record
    { Hom'         = Deduction
    ; isSetoid:Hom = record { _∼'_ = (λ f g -> ⟨ f ⟩ ≡ ⟨ g ⟩) ; isEquivRel:∼ = {!!} }
    ; id           = incl (′ id-𝒰 ′ {{id-Problem}})
    ; _◆_          = λ f g -> incl (′ ⟨ ⟨ f ⟩ ⟩ ◆-𝒰 ⟨ ⟨ g ⟩ ⟩ ′ {{comp-Problem {f = ⟨ f ⟩} {⟨ g ⟩}}})
    ; unit-l-◆   = incl refl
    ; unit-r-◆   = incl refl
    ; unit-2-◆   = incl refl
    ; assoc-l-◆  = incl refl
    ; assoc-r-◆  = incl refl
    ; _◈_        = {!!}
    }
{-
-}
