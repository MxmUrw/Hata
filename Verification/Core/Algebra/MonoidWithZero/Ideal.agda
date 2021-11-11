
module Verification.Core.Algebra.MonoidWithZero.Ideal where


open import Verification.Core.Algebra.MonoidWithZero.Ideal.Definition public
open import Verification.Core.Algebra.MonoidWithZero.Ideal.Principal public
open import Verification.Core.Algebra.MonoidWithZero.Ideal.Instance.Lattice public
open import Verification.Core.Algebra.MonoidWithZero.Ideal.Instance.hasAction public



--------------------------------------------------------------------------------------------------------------
{-
module _ {A : Monoid₀ 𝑖} where

  private
    _∼-Ideal_ : Idealᵣ A -> Idealᵣ A -> 𝒰 _
    _∼-Ideal_ = _∼-hasU_

  -- instance
  --   isEquivRel:∼-Ideal : isEquivRel (∼-Base _∼-Ideal_)
  --   isEquivRel:∼-Ideal = isEquivRel:hasU

  instance
    isSetoid:Idealᵣ : isSetoid (Idealᵣ A)
    isSetoid:Idealᵣ = isSetoid:hasU

  instance
    isIdealᵣ:⊤ : isIdealᵣ A ⊤
    isIdealᵣ.ideal-◍ isIdealᵣ:⊤ = tt
    isIdealᵣ.ideal-r-⋆ isIdealᵣ:⊤ _ _ = tt


  instance
    isPreorder:Idealᵣ : isPreorder _ ′(Idealᵣ A)′
    isPreorder._≤_ isPreorder:Idealᵣ I J = ⟨ I ⟩ ≤ ⟨ J ⟩
    isPreorder.reflexive isPreorder:Idealᵣ = λ a → reflexive
    isPreorder._⟡_ isPreorder:Idealᵣ = λ p q a → p a ⟡ q a
    isPreorder.transp-≤ isPreorder:Idealᵣ = {!!}
  --   isPreorder._≤_ isPreorder:Idealᵣ = (λ I J -> I ≤ J)
  --   isPreorder.reflexive isPreorder:Idealᵣ = ? -- incl (λ a -> a)
  --   isPreorder._⟡_ isPreorder:Idealᵣ p q = ? -- incl (λ a -> ⟨ q ⟩ (⟨ p ⟩ a)) -- ⟨( incl ⟨ p ⟩ ⟡ incl ⟨ q ⟩)⟩
  --   isPreorder.transp-≤ isPreorder:Idealᵣ p q X = ? -- incl ⟨ transp-≤ (⟨ p ⟩) (⟨ q ⟩) (incl ⟨ X ⟩) ⟩

  instance
    isPartialorder:Idealᵣ : isPartialorder ′(Idealᵣ A)′
    isPartialorder:Idealᵣ = record
      { antisym = λ p q -> incl $ antisym p q
      -- (incl (λ {_} -> ⟨ p ⟩)) (incl (λ {_} -> ⟨ q ⟩))
      -- antisym (incl ⟨ p ⟩) (incl ⟨ q ⟩)
      }

  -- instance
  --   hasAllJoins:Idealᵣ : hasAllJoins _ ′(Idealᵣ A)′
  --   hasAllJoins.⋁ hasAllJoins:Idealᵣ F = {!!}
  --   hasAllJoins.ι-⋁ hasAllJoins:Idealᵣ = {!!}
  --   hasAllJoins.[ hasAllJoins:Idealᵣ ]-⋁ = {!!}

  record _∧-Idealᵣ_ (I J : Idealᵣ A) (a : ⟨ A ⟩) : 𝒰 𝑖 where
    constructor _,_
    field fst : a ∈ I
    field snd : a ∈ J

  instance
    isIdealᵣ:∧ : ∀{I J : 𝒫 ⟨ A ⟩} -> {{_ : Idealᵣ A on I}} {{_ : Idealᵣ A on J}} -> isIdealᵣ A (′ I ′ ∧ ′ J ′)
    isIdealᵣ:∧ = record
      { ideal-◍ = ideal-◍ , ideal-◍
      ; ideal-r-⋆ = λ (p , q) a -> ideal-r-⋆ p a , ideal-r-⋆ q a
      }


  instance
    hasFiniteMeets:Idealᵣ : hasFiniteMeets ′(Idealᵣ A)′
    hasFiniteMeets.⊤ hasFiniteMeets:Idealᵣ = ′ ⊤ ′
    hasFiniteMeets.terminal-⊤ hasFiniteMeets:Idealᵣ = λ a -> incl (λ x → tt)
    hasFiniteMeets._∧_ hasFiniteMeets:Idealᵣ I J = ′ ⟨ I ⟩ ∧ ⟨ J ⟩ ′
    hasFiniteMeets.π₀-∧ hasFiniteMeets:Idealᵣ = λ a -> incl fst -- incl ⟨ π₀-∧ ⟩
    hasFiniteMeets.π₁-∧ hasFiniteMeets:Idealᵣ = λ a -> incl snd -- incl ⟨ π₁-∧ ⟩
    hasFiniteMeets.⟨_,_⟩-∧ hasFiniteMeets:Idealᵣ = {!!}
      -- λ f g a -> incl (λ x → (f a x , g a x))


module _ {A : Monoid₀ (𝑖 , 𝑖)} where

  record 0-Idealᵣᵘ (a : ⟨ A ⟩) : 𝒰 𝑖 where
    constructor incl
    field ⟨_⟩ : a ∼ ◍

  open 0-Idealᵣᵘ public

  macro 0-Idealᵣ = #structureOn (↓𝒫 0-Idealᵣᵘ)

  instance
    isSetoid:0-Idealᵣ : isSubsetoid 0-Idealᵣ
    isSetoid:0-Idealᵣ = {!!}

    isIdealᵣ:0-Idealᵣ : isIdealᵣ A (0-Idealᵣ)
    isIdealᵣ:0-Idealᵣ = {!!}


  -- module _ {I J : 𝒫 ⟨ A ⟩} {{_ : isSubsetoid I}} {{_ : isSubsetoid J}}
  --   {{_ : isIdealᵣ A ′ I ′}}
  --   {{_ : isIdealᵣ A ′ J ′}}
  --   where
  -- module _ {I J : 𝒫 ⟨ A ⟩} {{_ : Idealᵣ A on I}} {{_ : Idealᵣ A on J}} where
    -- distr-↷-∧-Ide : {a : ⟨ A ⟩} -> (a ↷ (′ I ′ ∧ ′ J ′)) ∼ ((a ↷ ′ I ′) ∧ (a ↷ ′ J ′))





-}



