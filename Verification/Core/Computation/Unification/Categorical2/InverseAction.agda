
module Verification.Core.Computation.Unification.Categorical2.InverseAction where

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
open import Verification.Core.Computation.Unification.Categorical2.ForwardAction
open import Verification.Core.Computation.Unification.Categorical2.SemilatticeStructure



-- ===* Inverse action on ideals
-- | Let |I : Ideal a| be an ideal at |a|, and |f : a ⟶ b| an arrow.
--   Then we define the ideal |f ↷⁻¹ I : Ideal b| to contain
--   those arrows |g : b ⟶ x|, such that |f ◆ g| is in |I|.
-- | Let |t s : a ⟶ b| be two terms considered as arrows.
--   We know that the coequalizer of them can be defined as
--   as an arrow through which every element of |CoeqIdeal a b| factors.
--   Now let |σ : b ⟶ c| be a substitution which is applied to |t| and |s|.
--   The coequalizer of |t ◆ σ| and |s ◆ σ| is now exactly an arrow through
--   which every element of |σ ↷⁻¹ CoeqIdeal a b| factors.



-- [Hide]
module _ {𝒞' : 𝐙𝐌𝐂𝐚𝐭 𝑖} where
  private
    𝒞 = ⟨ 𝒞' ⟩
    variable a b : 𝒞

  record _⁻¹↷ᵘ_ {a b : 𝒞} (f : a ⟶ b) (I : Ideal a) {x : 𝒞} (g : b ⟶ x) : 𝒰 (𝑖) where
    constructor incl
    field ⟨_⟩ : ⟨ I ⟩ (f ◆ g)

  open _⁻¹↷ᵘ_ public


  infixr 30 _⁻¹↷_
  _⁻¹↷_ : ∀{a b : 𝒞} -> (h : a ⟶ b) -> Ideal a -> Ideal b
  _⁻¹↷_ {a} {b} h I = (h ⁻¹↷ᵘ I) since P
    where
      lem-1 : {c : 𝒞} {f : b ⟶ c} {g : b ⟶ c} →
              f ∼ g → (h ⁻¹↷ᵘ I) f → (h ⁻¹↷ᵘ I) g
      lem-1 {c} {f} {g} f∼g (incl f∈hI) = incl (transp-Ideal (refl ◈ f∼g) f∈hI)

      lem-2 : {d : 𝒞} {f : b ⟶ d} →
                (h ⁻¹↷ᵘ I) f → {c : 𝒞} (g : d ⟶ c) → (h ⁻¹↷ᵘ I) (f ◆ g)
      lem-2 {d} {f} (incl f∈hI) {c} g =
        let P : ⟨ I ⟩ ((h ◆ f) ◆ g)
            P = ideal-r-◆ f∈hI g
            Q : ⟨ I ⟩ (h ◆ (f ◆ g))
            Q = transp-Ideal assoc-l-◆ P
        in incl Q

      P : isIdeal b _
      P = record
          { transp-Ideal = lem-1
          ; ideal-r-◆ = λ a b -> lem-2 a b
          ; ideal-pt = incl (transp-Ideal (absorb-r-◆ ⁻¹) ideal-pt)
          }

-- //

-- [Lemma]
-- | Let [..] be an arrow, and [..] an ideal.
  module _ {f : a ⟶ b} {I : Ideal a} where
    -- |> Then |↷| and |↷⁻¹| are almost inverses of each other.
    --   More concretely, the following is true:
    inv-↷-r : f ↷ (f ⁻¹↷ I) ∼ (I ∧ (f ↷ ⊤))

-- //

-- [Proof]
-- | Omitted.

-- //

-- [Hide]
    inv-↷-r = antisym
      (incl (λ h (incl (e , incl e∈f⁻¹I , fe∼h)) → transp-Ideal (fe∼h) (e∈f⁻¹I)  , (incl (e , (tt , fe∼h)))))
      (incl λ h (h∈I , incl (e , tt , fe∼h)) → incl (e , (incl (transp-Ideal (fe∼h ⁻¹) h∈I) , fe∼h)))

-- //


