
module Verification.Core.Computation.Unification.Categorical2.SemilatticeStructure where

open import Verification.Conventions
open import Verification.Core.Set.Setoid
open import Verification.Core.Order.Preorder
open import Verification.Core.Order.Lattice
open import Verification.Core.Order.WellFounded.Definition
open import Verification.Core.Data.Universe.Definition
open import Verification.Core.Data.Universe.Instance.Category
open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Category.Std.Category.Sized.Definition
open import Verification.Core.Category.Std.Morphism.Epi.Definition
open import Verification.Core.Category.Std.Category.As.ZeroMorphismCategory.Definition
open import Verification.Core.Computation.Unification.Categorical2.Ideal


-----------------------------------------------------------------------------------------
-- The semilattice structure

-- ===* Meet-semilattice structure of ideals
-- | Next, consider


-- [Hide]
module _ {𝒞 : 𝒰 𝑖}
         {{_ : isCategory {𝑗} 𝒞}}
         {{_ : isZeroMorphismCategory ′ 𝒞 ′}}
         where
  -- private
  --   𝒞 = ⟨ 𝒞' ⟩

  -- the meets
  module _ {a : 𝒞} (I J : Ideal a) where
    record _∧-Idealᵘ_ {b : 𝒞} (f : a ⟶ b) : 𝒰 (𝑖 ､ 𝑗) where
      constructor _,_
      field fst : ⟨ I ⟩ f
      field snd : ⟨ J ⟩ f

    open _∧-Idealᵘ_ public

    macro
      _∧-Ideal_ = #structureOn (λ {b} -> _∧-Idealᵘ_ {b})

  module _ {a : 𝒞} {I J : Ideal a} where
    instance
      isIdeal:∧-Ideal : isIdeal a (I ∧-Idealᵘ J)
      isIdeal:∧-Ideal = record
        { transp-Ideal = lem-1
        ; ideal-r-◆     = {!!} -- λ {_} -> lem-2 {_} {_}
        ; ideal-pt = ideal-pt , ideal-pt
        }
        where
          lem-1 : {b : 𝒞} {f g : a ⟶ b} → f ∼ g → (I ∧-Idealᵘ J) f → (I ∧-Idealᵘ J) g
          lem-1 p (A , B) = transp-Ideal p A , transp-Ideal p B

          lem-2 : {b : 𝒞} {f : a ⟶ b} → (I ∧-Idealᵘ J) f →
                  {c : 𝒞} (g : b ⟶ c) → (I ∧-Idealᵘ J) (f ◆ g)
          lem-2 (A , B) g = ideal-r-◆ A g , ideal-r-◆ B g

  -- the top element
  module _ {a : 𝒞} where
    record ⊤-Idealᵘ {b : 𝒞} (f : a ⟶ b) : 𝒰 (𝑖 ､ 𝑗) where
      constructor tt

    open ⊤-Idealᵘ public

    macro
      ⊤-Ideal = #structureOn (λ {b} -> ⊤-Idealᵘ {b})

    instance
      isIdeal:⊤-Ideal : isIdeal a ⊤-Ideal
      isIdeal:⊤-Ideal = record
        { transp-Ideal = λ p x → tt
        ; ideal-r-◆     = λ x g → tt
        }


    instance
      hasFiniteMeets:Ideal : hasFiniteMeets (Ideal a)
      hasFiniteMeets:Ideal = record
                                { ⊤ = ⊤-Ideal
                                ; terminal-⊤ = incl λ f x → tt
                                ; _∧_ = λ I J -> I ∧-Ideal J
                                ; π₀-∧ = incl λ f x → x .fst
                                ; π₁-∧ = incl λ f x → x .snd
                                ; ⟨_,_⟩-∧ = λ f g → incl λ h x → ⟨ f ⟩ h x , ⟨ g ⟩ h x
                                }

    module §-∧-Ideal where
      prop-1 : ∀{n : ℕ} {P : Fin-R n -> Ideal a} -> {x : 𝒞} {f : a ⟶ x} -> ⟨ ⋀-fin P ⟩ f -> ∀ i -> ⟨ P i ⟩ f
      prop-1 {zero} {P} {x} {f} f∈P ()
      prop-1 {suc n} {P} {x} {f} (f∈P0 , _   ) zero = f∈P0
      prop-1 {suc n} {P} {x} {f} (_    , f∈PS) (suc i) = prop-1 f∈PS i

      prop-2 : ∀{n : ℕ} {P : Fin-R n -> Ideal a} -> {x : 𝒞} {f : a ⟶ x} -> (∀ i -> ⟨ P i ⟩ f) -> ⟨ ⋀-fin P ⟩ f
      prop-2 {zero} {P} {x} {f} f∈Pi = tt
      prop-2 {suc n} {P} {x} {f} f∈Pi = f∈Pi zero , prop-2 (λ i -> f∈Pi (suc i))

      prop-3 : ∀{n : ℕ} -> ∀{b : 𝒞} -> {P : Fin-R n -> Ideal a} -> ⟨ ⋀-fin P ⟩ (pt {a = a} {b})
      prop-3 {P = P} = ideal-pt {{_}} {{of ⋀-fin P}}

-- //

