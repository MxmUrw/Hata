
{-# OPTIONS --experimental-lossy-unification #-}

module Verification.Core.Category.Std.Category.As.ZeroMorphismCategory.Coequalizer where

open import Verification.Conventions

open import Verification.Core.Set.Setoid.Definition
open import Verification.Core.Set.Contradiction
open import Verification.Core.Order.Preorder
open import Verification.Core.Order.Lattice
open import Verification.Core.Order.WellFounded.Definition
open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Category.Std.Category.Sized.Definition
open import Verification.Core.Category.Std.Category.As.ZeroMorphismCategory.Definition
open import Verification.Core.Computation.Unification.Categorical.Definition
open import Verification.Core.Category.Std.Limit.Specific.Coequalizer

module _ {A : 𝒰 𝑖} {{_ : isSetoid {𝑗} A}} where
  by-≣-∼ : ∀{a b : A} -> a ≣ b -> a ∼ b
  by-≣-∼ refl-≣ = refl

module _ {𝒞 : 𝒰 _}
       {{_ : isCategory {𝑖} {𝑗} 𝒞}}
       {{_ : isZeroMorphismCategory ′ 𝒞 ′}}
       where

  -- CoeqHoms : ∀{a b : ⟨ 𝒞 ⟩} -> (f g : a ⟶ b) -> UpFamily b
  -- CoeqHoms f g = {!!}

  module _ {a b : 𝒞} (f g : a ⟶ b) where

    record CoeqIdealᵘ {x : 𝒞} (h : b ⟶ x) : 𝒰 (𝑖 ､ 𝑗) where
      constructor incl
      field ⟨_⟩ : f ◆ h ∼ g ◆ h

    open CoeqIdealᵘ public

    macro CoeqIdeal = #structureOn (λ {x} -> CoeqIdealᵘ {x})

  module _ {a b : 𝒞} {f g : a ⟶ b} where
    instance
      isIdealᵣ:CoeqIdeal : isIdealᵣ b (CoeqIdealᵘ f g)
      isIdealᵣ:CoeqIdeal = record
        { transp-Idealᵣ = lem-1
        ; ideal-r-◆ = lem-2
        ; ideal-pt = lem-3
        }
        where
          lem-1 : ∀{x} {h0 h1 : b ⟶ x} -> (h0 ∼ h1) -> CoeqIdeal f g h0 -> CoeqIdeal f g h1
          lem-1 h0∼h1 (incl P) = incl ((refl ◈ h0∼h1 ⁻¹) ∙ P ∙ (refl ◈ h0∼h1))

          lem-2 : ∀{x} {h₀ : b ⟶ x} -> CoeqIdeal f g h₀ -> ∀{c} -> (h₁ : x ⟶ c) -> CoeqIdeal f g (h₀ ◆ h₁)
          lem-2 (incl P) h₁ = incl (assoc-r-◆ ∙ (P ◈ refl) ∙ assoc-l-◆)

          lem-3 : ∀{x : 𝒞} -> CoeqIdealᵘ f g {x} pt
          lem-3 = incl (absorb-r-◆ ∙ absorb-r-◆ ⁻¹)

module _ {𝒞 : Category 𝑖} {{_ : isSizedCategory 𝒞}} where

  asIdealᵣ : ∀{a b : ⟨ 𝒞 ⟩} -> HomPair a b -> Idealᵣ {𝒞 = Free-𝐙𝐌𝐂𝐚𝐭 𝒞} (incl b)
  asIdealᵣ (f , g) = CoeqIdeal (some f) (some g)


  module _ {a b : ⟨ 𝒞 ⟩} where
    private
      lem-1 : {p : HomPair a b} -> {x : Free-𝐙𝐌𝐂𝐚𝐭 𝒞} {h : incl b ⟶ x} -> ⟨ asIdealᵣ p ⟩ h -> (h ∼ pt) +-𝒰 hasCoequalizerCandidate p
      lem-1 {p} {incl x} {some f} (incl (some Q)) = right (x since record { π₌? = f ; equate-π₌? = Q })
      lem-1 {p} {x} {zero} Q = left zero

      lem-4 : {p : HomPair a b} -> hasCoequalizerCandidate p -> ∑ λ (x : ⟨ 𝒞 ⟩) -> ∑ λ (h : b ⟶ x) -> ⟨ asIdealᵣ p ⟩ (some h)
      lem-4 {p} (j since jP) = j , π₌? , incl (some equate-π₌?)


    Forward : {f : HomPair a b} -> hasSizedCoequalizerDecision f -> isEpiPrincipalᵣ (asIdealᵣ f)
    Forward {f} (left noCandidate) =
      let ⟨f⟩∼⊥ : asIdealᵣ f ∼ ⊥-Idealᵣ
          ⟨f⟩∼⊥ = antisym
                  (incl (λ h h∈⟨f⟩ → case lem-1 h∈⟨f⟩ of
                                    incl
                                    λ candidate → impossible (noCandidate candidate)))
                  initial-⊥-Idealᵣ
      in transp-isEpiPrincipalᵣ (⟨f⟩∼⊥ ⁻¹) isEpiPrincipalᵣ:⊥
    Forward {f , g} (just (x , sizedx)) = record
      { repObj = incl ⟨ x ⟩
      ; rep = some π₌
      ; principal-r = antisym lem-2 lem-3
      ; isGoodRep = lem-5
      ; zeroOrEpi = right (preserve-isEpi-Free-𝐙𝐌𝐂𝐚𝐭 isEpi:π₌)
      }
      where
        instance _ = of x

        lem-2 : asIdealᵣ (f , g) ≤ (some π₌ ↷ ⊤)
        ⟨ lem-2 ⟩ (some h) (incl (some fh∼gh)) = incl (some ⦗ h , fh∼gh ⦘₌ , tt , some reduce-π₌)
        ⟨ lem-2 ⟩ zero x = incl (pt , tt , refl)

        lem-3 : (some π₌ ↷ ⊤) ≤ asIdealᵣ (f , g)
        ⟨ lem-3 ⟩ (some h) (incl (e , tt , π₌e∼h)) = incl P
          where
            P : some (f ◆ h) ∼ some (g ◆ h)
            P = equate-π₌
                >> f ◆ π₌ ∼ g ◆ π₌ <<
                ⟪ some ⟫
                >> some f ◆ some π₌ ∼ some g ◆ some π₌ <<
                ⟪ _◈ refl ⟫
                >> some f ◆ some π₌ ◆ e ∼ some g ◆ some π₌ ◆ e <<
                ⟪ assoc-l-◆ ≀∼≀ assoc-l-◆ ⟫
                >> some f ◆ (some π₌ ◆ e) ∼ some g ◆ (some π₌ ◆ e) <<
                ⟪ refl ◈ π₌e∼h ≀∼≀ refl ◈ π₌e∼h ⟫
                >> some f ◆ some h ∼ some g ◆ some h <<

        ⟨ lem-3 ⟩ zero x = incl refl

        lem-5 : isGood (some π₌)
        lem-5 = case sizedx of
                  (λ {(incl p) → right (left (incl (some p)))})
                  λ sized → right (right sized)



    Backward : {f : HomPair a b} -> isEpiPrincipalᵣ (asIdealᵣ f) -> hasSizedCoequalizerDecision f
    Backward {f , g} P with zeroOrEpi {{_}} {{P}}
    ... | left rep∼pt = left Proof
      where
        module _ (Q : hasCoequalizerCandidate (f , g)) where
          instance _ = of Q
          instance _ = P

          lem-3 : asIdealᵣ (f , g) ∼ ⊥-Idealᵣ
          lem-3 = §-EpiPrincipalᵣ.prop-1 rep∼pt

          Proof : 𝟘-𝒰
          Proof with lem-4 Q
          ... | (x , h , hp) with ⟨ by-∼-≤ lem-3 ⟩ _ hp
          ... | ()

    ... | just isEpi:rep with rep {{_}} {{P}} in rep≣π'
    ... | zero = impossible (¬isEpi:zero isEpi:rep)
    ... | some π' = right (x since lem-10 , lem-9)
      where
        instance _ = P
        x : ⟨ 𝒞 ⟩
        x = ⟨ repObjOf (asIdealᵣ (f , g)) ⟩

        lem-5 : ⟨ asIdealᵣ (f , g) ⟩ rep
        lem-5 = §-EpiPrincipalᵣ.prop-2

        lem-6 : ⟨ asIdealᵣ (f , g) ⟩ (some π')
        lem-6 = transport-Str (cong-Str (λ ξ -> ⟨ asIdealᵣ (f , g) ⟩ ξ) (rep≣π')) lem-5

        lem-7 : f ◆ π' ∼ g ◆ π'
        lem-7 with lem-6
        ... | incl (some p) = p

        lem-8 : ∀{d : ⟨ 𝒞 ⟩} -> (h : b ⟶ d) -> f ◆ h ∼ g ◆ h -> ∑ λ (h' : x ⟶ d) -> π' ◆ h' ∼ h
        lem-8 {d} h fh∼gh = lem-8-4
          where
            lem-8-1 : ⟨ asIdealᵣ (f , g) ⟩ (some h)
            lem-8-1 = incl (some fh∼gh)

            lem-8-2 : ⟨ rep ↷ ⊤ ⟩ (some h)
            lem-8-2 = ⟨ (by-∼-≤ principal-r) ⟩ _ lem-8-1

            lem-8-3 : ⟨ some π' ↷ ⊤ ⟩ (some h)
            lem-8-3 = transport-Str (cong-Str (λ ξ -> ⟨ ξ ↷ ⊤-Idealᵣ ⟩ (some h)) rep≣π') lem-8-2

            lem-8-4 : ∑ λ (h' : x ⟶ d) -> π' ◆ h' ∼ h
            lem-8-4 with lem-8-3
            ... | incl (some e , tt , some π'e∼h) = e , π'e∼h

        lem-9 : isId π' +-𝒰 (sizeO x ≪ sizeO b)
        lem-9 with isGoodRep {{_}} {{P}}
        ... | left (incl rep∼zero) = impossible (rep∼zero ⁻¹ ∙ (by-≣-∼ rep≣π'))
        ... | just (left (incl rep∼id)) = left $ incl (cancel-injective-some-Free-𝐙𝐌𝐂𝐚𝐭 (by-≣-∼ rep≣π' ⁻¹ ∙ rep∼id))
        ... | just (just sized) = right sized

        lem-10 : isCoequalizer f g x
        isCoequalizer.π₌ lem-10 = π'
        isCoequalizer.equate-π₌ lem-10 = lem-7
        isCoequalizer.compute-Coeq lem-10 = lem-8
        isCoequalizer.isEpi:π₌ lem-10 = reflect-isEpi-Free-𝐙𝐌𝐂𝐚𝐭 isEpi:rep






