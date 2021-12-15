
module Verification.Core.Algebra.MonoidWithZero.Ideal where


open import Verification.Core.Algebra.MonoidWithZero.Ideal.Definition public
open import Verification.Core.Algebra.MonoidWithZero.Ideal.Principal public
open import Verification.Core.Algebra.MonoidWithZero.Ideal.Instance.Lattice public
open import Verification.Core.Algebra.MonoidWithZero.Ideal.Instance.hasAction public



--------------------------------------------------------------------------------------------------------------
{-
module _ {A : Monoid₀ 𝑖} where

  private
    _∼-Ideal_ : Ideal A -> Ideal A -> 𝒰 _
    _∼-Ideal_ = _∼-hasU_

  -- instance
  --   isEquivRel:∼-Ideal : isEquivRel (∼-Base _∼-Ideal_)
  --   isEquivRel:∼-Ideal = isEquivRel:hasU

  instance
    isSetoid:Ideal : isSetoid (Ideal A)
    isSetoid:Ideal = isSetoid:hasU

  instance
    isIdeal:⊤ : isIdeal A ⊤
    isIdeal.ideal-◍ isIdeal:⊤ = tt
    isIdeal.ideal-r-⋆ isIdeal:⊤ _ _ = tt


  instance
    isPreorder:Ideal : isPreorder _ ′(Ideal A)′
    isPreorder._≤_ isPreorder:Ideal I J = ⟨ I ⟩ ≤ ⟨ J ⟩
    isPreorder.reflexive isPreorder:Ideal = λ a → reflexive
    isPreorder._⟡_ isPreorder:Ideal = λ p q a → p a ⟡ q a
    isPreorder.transp-≤ isPreorder:Ideal = {!!}
  --   isPreorder._≤_ isPreorder:Ideal = (λ I J -> I ≤ J)
  --   isPreorder.reflexive isPreorder:Ideal = ? -- incl (λ a -> a)
  --   isPreorder._⟡_ isPreorder:Ideal p q = ? -- incl (λ a -> ⟨ q ⟩ (⟨ p ⟩ a)) -- ⟨( incl ⟨ p ⟩ ⟡ incl ⟨ q ⟩)⟩
  --   isPreorder.transp-≤ isPreorder:Ideal p q X = ? -- incl ⟨ transp-≤ (⟨ p ⟩) (⟨ q ⟩) (incl ⟨ X ⟩) ⟩

  instance
    isPartialorder:Ideal : isPartialorder ′(Ideal A)′
    isPartialorder:Ideal = record
      { antisym = λ p q -> incl $ antisym p q
      -- (incl (λ {_} -> ⟨ p ⟩)) (incl (λ {_} -> ⟨ q ⟩))
      -- antisym (incl ⟨ p ⟩) (incl ⟨ q ⟩)
      }

  -- instance
  --   hasAllJoins:Ideal : hasAllJoins _ ′(Ideal A)′
  --   hasAllJoins.⋁ hasAllJoins:Ideal F = {!!}
  --   hasAllJoins.ι-⋁ hasAllJoins:Ideal = {!!}
  --   hasAllJoins.[ hasAllJoins:Ideal ]-⋁ = {!!}

  record _∧-Ideal_ (I J : Ideal A) (a : ⟨ A ⟩) : 𝒰 𝑖 where
    constructor _,_
    field fst : a ∈ I
    field snd : a ∈ J

  instance
    isIdeal:∧ : ∀{I J : 𝒫 ⟨ A ⟩} -> {{_ : Ideal A on I}} {{_ : Ideal A on J}} -> isIdeal A (′ I ′ ∧ ′ J ′)
    isIdeal:∧ = record
      { ideal-◍ = ideal-◍ , ideal-◍
      ; ideal-r-⋆ = λ (p , q) a -> ideal-r-⋆ p a , ideal-r-⋆ q a
      }


  instance
    hasFiniteMeets:Ideal : hasFiniteMeets ′(Ideal A)′
    hasFiniteMeets.⊤ hasFiniteMeets:Ideal = ′ ⊤ ′
    hasFiniteMeets.terminal-⊤ hasFiniteMeets:Ideal = λ a -> incl (λ x → tt)
    hasFiniteMeets._∧_ hasFiniteMeets:Ideal I J = ′ ⟨ I ⟩ ∧ ⟨ J ⟩ ′
    hasFiniteMeets.π₀-∧ hasFiniteMeets:Ideal = λ a -> incl fst -- incl ⟨ π₀-∧ ⟩
    hasFiniteMeets.π₁-∧ hasFiniteMeets:Ideal = λ a -> incl snd -- incl ⟨ π₁-∧ ⟩
    hasFiniteMeets.⟨_,_⟩-∧ hasFiniteMeets:Ideal = {!!}
      -- λ f g a -> incl (λ x → (f a x , g a x))


module _ {A : Monoid₀ (𝑖 , 𝑖)} where

  record 0-Idealᵘ (a : ⟨ A ⟩) : 𝒰 𝑖 where
    constructor incl
    field ⟨_⟩ : a ∼ ◍

  open 0-Idealᵘ public

  macro 0-Ideal = #structureOn (↓𝒫 0-Idealᵘ)

  instance
    isSetoid:0-Ideal : isSubsetoid 0-Ideal
    isSetoid:0-Ideal = {!!}

    isIdeal:0-Ideal : isIdeal A (0-Ideal)
    isIdeal:0-Ideal = {!!}


  -- module _ {I J : 𝒫 ⟨ A ⟩} {{_ : isSubsetoid I}} {{_ : isSubsetoid J}}
  --   {{_ : isIdeal A ′ I ′}}
  --   {{_ : isIdeal A ′ J ′}}
  --   where
  -- module _ {I J : 𝒫 ⟨ A ⟩} {{_ : Ideal A on I}} {{_ : Ideal A on J}} where
    -- distr-↷-∧-Ide : {a : ⟨ A ⟩} -> (a ↷ (′ I ′ ∧ ′ J ′)) ∼ ((a ↷ ′ I ′) ∧ (a ↷ ′ J ′))





-}



