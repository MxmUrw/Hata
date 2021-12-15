
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
  module _ {a : 𝒞} (I J : Idealᵣ a) where
    record _∧-Idealᵣᵘ_ {b : 𝒞} (f : a ⟶ b) : 𝒰 (𝑖 ､ 𝑗) where
      constructor _,_
      field fst : ⟨ I ⟩ f
      field snd : ⟨ J ⟩ f

    open _∧-Idealᵣᵘ_ public

    macro
      _∧-Idealᵣ_ = #structureOn (λ {b} -> _∧-Idealᵣᵘ_ {b})

  module _ {a : 𝒞} {I J : Idealᵣ a} where
    instance
      isIdealᵣ:∧-Idealᵣ : isIdealᵣ a (I ∧-Idealᵣᵘ J)
      isIdealᵣ:∧-Idealᵣ = record
        { transp-Idealᵣ = lem-1
        ; ideal-r-◆     = {!!} -- λ {_} -> lem-2 {_} {_}
        ; ideal-pt = ideal-pt , ideal-pt
        }
        where
          lem-1 : {b : 𝒞} {f g : a ⟶ b} → f ∼ g → (I ∧-Idealᵣᵘ J) f → (I ∧-Idealᵣᵘ J) g
          lem-1 p (A , B) = transp-Idealᵣ p A , transp-Idealᵣ p B

          lem-2 : {b : 𝒞} {f : a ⟶ b} → (I ∧-Idealᵣᵘ J) f →
                  {c : 𝒞} (g : b ⟶ c) → (I ∧-Idealᵣᵘ J) (f ◆ g)
          lem-2 (A , B) g = ideal-r-◆ A g , ideal-r-◆ B g

  -- the top element
  module _ {a : 𝒞} where
    record ⊤-Idealᵣᵘ {b : 𝒞} (f : a ⟶ b) : 𝒰 (𝑖 ､ 𝑗) where
      constructor tt

    open ⊤-Idealᵣᵘ public

    macro
      ⊤-Idealᵣ = #structureOn (λ {b} -> ⊤-Idealᵣᵘ {b})

    instance
      isIdealᵣ:⊤-Idealᵣ : isIdealᵣ a ⊤-Idealᵣ
      isIdealᵣ:⊤-Idealᵣ = record
        { transp-Idealᵣ = λ p x → tt
        ; ideal-r-◆     = λ x g → tt
        }


    instance
      hasFiniteMeets:Idealᵣ : hasFiniteMeets (Idealᵣ a)
      hasFiniteMeets:Idealᵣ = record
                                { ⊤ = ⊤-Idealᵣ
                                ; terminal-⊤ = incl λ f x → tt
                                ; _∧_ = λ I J -> I ∧-Idealᵣ J
                                ; π₀-∧ = incl λ f x → x .fst
                                ; π₁-∧ = incl λ f x → x .snd
                                ; ⟨_,_⟩-∧ = λ f g → incl λ h x → ⟨ f ⟩ h x , ⟨ g ⟩ h x
                                }

    module §-∧-Idealᵣ where
      prop-1 : ∀{n : ℕ} {P : Fin-R n -> Idealᵣ a} -> {x : 𝒞} {f : a ⟶ x} -> ⟨ ⋀-fin P ⟩ f -> ∀ i -> ⟨ P i ⟩ f
      prop-1 {zero} {P} {x} {f} f∈P ()
      prop-1 {suc n} {P} {x} {f} (f∈P0 , _   ) zero = f∈P0
      prop-1 {suc n} {P} {x} {f} (_    , f∈PS) (suc i) = prop-1 f∈PS i

      prop-2 : ∀{n : ℕ} {P : Fin-R n -> Idealᵣ a} -> {x : 𝒞} {f : a ⟶ x} -> (∀ i -> ⟨ P i ⟩ f) -> ⟨ ⋀-fin P ⟩ f
      prop-2 {zero} {P} {x} {f} f∈Pi = tt
      prop-2 {suc n} {P} {x} {f} f∈Pi = f∈Pi zero , prop-2 (λ i -> f∈Pi (suc i))

      prop-3 : ∀{n : ℕ} -> ∀{b : 𝒞} -> {P : Fin-R n -> Idealᵣ a} -> ⟨ ⋀-fin P ⟩ (pt {a = a} {b})
      prop-3 {P = P} = ideal-pt {{_}} {{of ⋀-fin P}}

-- //

