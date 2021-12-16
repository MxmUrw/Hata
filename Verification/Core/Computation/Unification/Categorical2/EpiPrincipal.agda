
module Verification.Core.Computation.Unification.Categorical2.EpiPrincipal where

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
open import Verification.Core.Computation.Unification.Categorical2.ZeroIdeal

-- [Hide]

module _ (𝒞 : Category 𝑖) where
  HomFamily : ∀ 𝑗 -> 𝒰 _
  HomFamily 𝑗 = ∀{a b : ⟨ 𝒞 ⟩} -> (f : a ⟶ b) -> 𝒰 𝑗

module _ {𝒞 : 𝒰 𝑖} {{_ : isCategory {𝑗} 𝒞}} where
  module _ {{_ : isZeroMorphismCategory ′ 𝒞 ′}} where

    record isPt {a b : 𝒞} (f : a ⟶ b) : 𝒰 (𝑖 ､ 𝑗) where
      constructor incl
      field ⟨_⟩ : f ∼ pt
      -- -> isPt {a} {b} f

    open isPt public


module _ {𝒞 : Category 𝑖} {{_ : isSizedCategory 𝒞}} {{_ : isZeroMorphismCategory 𝒞}} where

  isGood : HomFamily 𝒞 _
  isGood {a} {b} g = isPt g +-𝒰 (isId g +-𝒰 (sizeO b ≪ sizeO a))

  transp-isGood : ∀{a b : ⟨ 𝒞 ⟩} {f g : a ⟶ b} -> f ∼ g -> isGood f -> isGood g
  transp-isGood f∼g (left (incl f∼pt)) = left (incl (f∼g ⁻¹ ∙ f∼pt))
  transp-isGood f∼g (just (left (incl f∼id))) = just (left (incl (f∼g ⁻¹ ∙ f∼id)))
  transp-isGood f∼g (just (just x)) = just (just x)

  isGood:◆ : ∀{a b c : ⟨ 𝒞 ⟩} {f : a ⟶ b} {g : b ⟶ c} -> isGood f -> isGood g -> isGood (f ◆ g)
  isGood:◆ (left (incl f∼pt)) (q) = left (incl ((f∼pt ◈ refl) ∙ absorb-l-◆))
  isGood:◆ (just (left (incl f∼id))) q = transp-isGood (unit-l-◆ ⁻¹ ∙ (f∼id ⁻¹ ◈ refl)) q
  isGood:◆ (just (just x)) (left (incl g∼pt)) = left (incl ((refl ◈ g∼pt) ∙ absorb-r-◆))
  isGood:◆ (just (just x)) (just (left (incl _))) = just (just x)
  isGood:◆ (just (just x)) (just (just y)) = just (just (y ⟡-≪ x))

module _ {𝒞' : 𝐙𝐌𝐂𝐚𝐭 𝑖} {{_ : isSizedCategory ′ ⟨ 𝒞' ⟩ ′}} where
  private
    𝒞 = ⟨ 𝒞' ⟩
    variable a b c : 𝒞
-- //

-- ===* Epi-principal ideals
-- | We have seen that an epimorphism |π : a ⟶ b| such that |I ∼ π ↷ ⊤|
--   captures the notion of a coequalizer. It would be useful if we could
--   say that, given some ideal |I|, the goal of unification is to find exactly such an
--   epimorphism |π|. But there is one problem:
--   If |t| and |s| are not unifiable, then |I| is the zero ideal.
--   We then have |I ∼ pt ↷ ⊤|. But, even though |pt| fulfills this equation,
--   it is not an epimorphism: |pt ◆ f ∼ pt ◆ g| does not imply |f ∼ g|.
--   Thus, we have to relax the requirement on |π|, we define the following:


  isZeroOrEpi : (f : a ⟶ b) -> 𝒰 _
  isZeroOrEpi f = (f ∼ pt) +-𝒰 (isEpi f)

  -- [Hide]
  isZeroOrEpi:◆ : ∀{a b c : 𝒞} -> {f : a ⟶ b} {g : b ⟶ c} -> isZeroOrEpi f -> isZeroOrEpi g
                  -> isZeroOrEpi (f ◆ g)
  isZeroOrEpi:◆ (left f∼pt) q = left ((f∼pt ◈ refl) ∙ absorb-l-◆)
  isZeroOrEpi:◆ (just x) (left g∼pt) = left ((refl ◈ g∼pt) ∙ absorb-r-◆)
  isZeroOrEpi:◆ (just x) (just y) = just (isEpi:◆ x y)
  -- //


-- [Definition]
-- | Let |I| be an ideal at |a|. We say that it
--   is /epi-principal/ if the following data is
--   given: []
  record isEpiPrincipal (I : Ideal a) : 𝒰 (𝑖) where
    -- | 1. An object [..].
    field repObj : 𝒞
    -- | 2. An arrow [..] said to be representing this ideal.
    field rep : a ⟶ repObj
    -- | 3. Such that the equation [..] holds.
    field principal-r : I ∼ rep ↷ ⊤
    -- | 4. Finally, we want the representing arrow
    --      to be either zero, or an epimorphism.
    field zeroOrEpi : isZeroOrEpi rep
    -- //


-- [Hide]
    field isGoodRep : isGood rep

    -- field factorPrinc : ∀{x} -> (f : a ⟶ x) -> ⟨ I ⟩ f -> ∑ λ (g : repObj ⟶ x) -> f ∼ rep ◆ g

  open isEpiPrincipal {{...}} public

  repObjOf : (I : Ideal a) {{_ : isEpiPrincipal I}} -> 𝒞
  repObjOf I = repObj

  repOf : (I : Ideal a) {{_ : isEpiPrincipal I}} -> a ⟶ repObjOf I
  repOf I = rep

  module _ {a : 𝒞} where
    instance
      isEpiPrincipal:⊤ : isEpiPrincipal ⊤
      isEpiPrincipal:⊤ = record
        { repObj = a
        ; rep = id
        ; principal-r = antisym lem-1 terminal-⊤
        ; isGoodRep = right (left (incl refl))
        ; zeroOrEpi = right (isEpi:id)
        }
        where
          lem-1 : ⊤ ≤ (id ↷ ⊤)
          lem-1 = incl λ f x → incl (f , (x , unit-l-◆))

    transp-isEpiPrincipal : ∀{I J : Ideal a} -> (I ∼ J) -> isEpiPrincipal I -> isEpiPrincipal J
    transp-isEpiPrincipal {I} {J} I∼J P =
      let
        instance _ = P
      in record
        { repObj = repObjOf I
        ; rep = repOf I
        ; principal-r = I∼J ⁻¹ ∙ principal-r
        ; isGoodRep = isGoodRep
        ; zeroOrEpi = zeroOrEpi
        }

    instance
      isEpiPrincipal:⊥ : isEpiPrincipal ⊥-Ideal
      isEpiPrincipal:⊥ = record
        { repObj = a
        ; rep = pt
        ; principal-r = antisym initial-⊥-Ideal lem-1
        ; isGoodRep = left (incl refl)
        ; zeroOrEpi = left refl
        }
        where
          lem-1 : (pt {a = a} {a} ↷ ⊤-Ideal) ≤ ⊥-Ideal
          lem-1 = incl λ f (incl (e , tt , pt◆e∼f)) → incl (pt◆e∼f ⁻¹ ∙ absorb-l-◆)

    module §-EpiPrincipalᵣ where

      prop-1 : ∀{I : Ideal a} {{_ : isEpiPrincipal I}} -> repOf I ∼ pt -> I ∼ ⊥-Ideal
      prop-1 {I} p = principal-r ∙ (p ≀↷≀ refl) ∙ P
        where
          P : (pt {a = a} {repObjOf I} ↷ ⊤-Ideal) ∼ ⊥-Ideal
          P = antisym
              (incl (λ f (incl (e , _ , pt◆e∼f)) →
                let pt∼f : pt ∼ f
                    pt∼f = absorb-l-◆ ⁻¹ ∙ pt◆e∼f
                in incl (pt∼f ⁻¹)
              ))
              initial-⊥-Ideal

      prop-2 : ∀{I : Ideal a} {{_ : isEpiPrincipal I}} -> ⟨ I ⟩ (repOf I)
      prop-2 {I} {{IP}} = ⟨ by-∼-≤ (principal-r {{IP}} ⁻¹) ⟩ _ (incl (id , (tt , unit-r-◆)))

-- //


