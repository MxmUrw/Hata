
module Verification.Experimental.Computation.Question.Definition where

open import Verification.Experimental.Conventions hiding (Forget)
open import Verification.Experimental.Set.Setoid.Definition
open import Verification.Experimental.Data.Universe.Everything
open import Verification.Experimental.Data.Prop.Everything
open import Verification.Experimental.Order.WellFounded.Definition
open import Verification.Experimental.Order.Preorder
open import Verification.Experimental.Category.Std.Category.Definition
open import Verification.Experimental.Category.Std.Functor.Definition



---------------------------------------------------------------
-- Definition of a question


record isQuestion (𝑖 : 𝔏) (𝔔 : 𝒰 𝑗) : 𝒰 (𝑖 ⁺ ､ 𝑗) where
  constructor answerWith
  field _‽ : (𝔔 -> 𝒰 𝑖)
  infix 300 _‽

open isQuestion {{...}} public

Question : (𝑖 : 𝔏 ^ 2) -> 𝒰 _
Question 𝑖 = 𝒰' (𝑖 ⌄ 0) :& isQuestion (𝑖 ⌄ 1)

macro
  𝐐𝐮𝐞𝐬𝐭 : ∀ (𝑖 : 𝔏 ^ 2) -> SomeStructure
  𝐐𝐮𝐞𝐬𝐭 𝑖 = #structureOn (Question 𝑖)

isSolved : (𝔔 : 𝐐𝐮𝐞𝐬𝐭 𝑖) -> 𝒰 _
isSolved 𝔔 = ∀ (q : ⟨ 𝔔 ⟩) -> q ‽

---------------------------------------------------------------
-- The set of questions has itself a question structure

instance
  isQuestion:𝐐𝐮𝐞𝐬𝐭 : isQuestion _ (𝐐𝐮𝐞𝐬𝐭 𝑖)
  isQuestion:𝐐𝐮𝐞𝐬𝐭 = answerWith isSolved

---------------------------------------------------------------
-- Definition of question morphisms

module _ (𝔔 : 𝐐𝐮𝐞𝐬𝐭 (𝑖 , 𝑘)) (ℜ : 𝐐𝐮𝐞𝐬𝐭 (𝑗 , 𝑘)) where
  record isReductive (f : ⟨ 𝔔 ⟩ -> ⟨ ℜ ⟩) : 𝒰 (𝑖 ､ 𝑘) where
    constructor reductive
    field reduce : ∀{q : ⟨ 𝔔 ⟩} -> f q ‽ -> q ‽

  open isReductive {{...}} public

  Reduction : 𝒰 _
  Reduction = _ :& isReductive

private
  instance
    id-Question : ∀{A : Question 𝑖} -> isReductive A A id-𝒰
    id-Question = record
      { reduce = λ x → x
      }

  instance
    comp-Question : ∀{A B C : Question 𝑖} -> {f : Reduction A B} -> {g : Reduction B C} -> isReductive A C (⟨ f ⟩ ◆-𝒰 ⟨ g ⟩)
    comp-Question {f = f} {g = g} = record
      { reduce = λ x → reduce {{of f}} (reduce {{of g}} x)
      }

---------------------------------------------------------------
-- The category of questions

instance
  isCategory:𝐐𝐮𝐞𝐬𝐭 : isCategory _ (𝐐𝐮𝐞𝐬𝐭 𝑖)
  isCategory:𝐐𝐮𝐞𝐬𝐭 =
    record
    { Hom'         = Reduction
    ; isSetoid:Hom = record { _∼'_ = (λ f g -> ⟨ f ⟩ ≡ ⟨ g ⟩) ; isEquivRel:∼ = {!!} }
    ; id           = incl (′ id-𝒰 ′ {{id-Question}})
    ; _◆_          = λ f g -> incl (′ ⟨ ⟨ f ⟩ ⟩ ◆-𝒰 ⟨ ⟨ g ⟩ ⟩ ′ {{comp-Question {f = ⟨ f ⟩} {⟨ g ⟩}}})
    ; unit-l-◆   = incl refl
    ; unit-r-◆   = incl refl
    ; unit-2-◆   = incl refl
    ; assoc-l-◆  = incl refl
    ; assoc-r-◆  = incl refl
    ; _◈_        = {!!}
    }

private
  Forget : 𝐐𝐮𝐞𝐬𝐭 𝑖 -> 𝐓𝐲𝐩𝐞 _
  Forget 𝔔 = ⟨ 𝔔 ⟩

instance
  Register:ForgetQuestion = register₁[ "" , 𝑖 ] Forget {𝑖}

instance
  isFunctor:ForgetQuestion : isFunctor (𝐐𝐮𝐞𝐬𝐭 𝑖) (𝐓𝐲𝐩𝐞 _) Forget
  isFunctor.map isFunctor:ForgetQuestion = λ f -> incl ⟨ ⟨ f ⟩ ⟩
  isFunctor.isSetoidHom:map isFunctor:ForgetQuestion = {!!}
  isFunctor.functoriality-id isFunctor:ForgetQuestion = {!!}
  isFunctor.functoriality-◆ isFunctor:ForgetQuestion = {!!}




