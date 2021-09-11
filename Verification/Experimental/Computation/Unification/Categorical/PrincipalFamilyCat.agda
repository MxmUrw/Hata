
module Verification.Experimental.Computation.Unification.Categorical.PrincipalFamilyCat where

open import Verification.Conventions

open import Verification.Experimental.Category.Std.Category.Definition
open import Verification.Experimental.Category.Std.Limit.Specific.Coequalizer
open import Verification.Experimental.Set.Setoid.Definition
open import Verification.Experimental.Set.Setoid.Subsetoid
open import Verification.Experimental.Set.Decidable
open import Verification.Experimental.Set.Discrete
open import Verification.Experimental.Data.Prop.Everything
open import Verification.Experimental.Data.Universe.Everything
open import Verification.Experimental.Data.Sum.Definition
open import Verification.Experimental.Data.Nat.Free
-- open import Verification.Experimental.Data.Indexed.Definition
open import Verification.Experimental.Order.Preorder
open import Verification.Experimental.Order.Lattice
open import Verification.Experimental.Order.WellFounded.Definition
open import Verification.Experimental.Computation.Unification.Definition
open import Verification.Experimental.Computation.Unification.Categorical.PrincipalFamily
-- open import Verification.Experimental.Theory.Presentation.Signature.Definition


module _ {M : 𝒰 𝑖} {{_ : Monoid₀ (𝑖 , 𝑖) on M}} where

  record CoeqSolutions' (f g h : M) : 𝒰 𝑖 where
    constructor incl
    field ⟨_⟩ : f ⋆ h ∼ g ⋆ h
  open CoeqSolutions' public

  CoeqSolutions : (f g : M) -> 𝒫 M
  CoeqSolutions f g = λ h -> ∣ CoeqSolutions' f g h ∣

module _ {𝒞 : 𝒰 𝑖} {{_ : isCategory {𝑗} 𝒞}} where
  record hasProperty-isCoeq {a b x : 𝒞} (f : (a ⟶ b) ^ 2) (h : b ⟶ x) : 𝒰 (𝑖 ､ 𝑗) where
    constructor incl
    field ⟨_⟩ : fst f ◆ h ∼ snd f ◆ h

module _ {M : Monoid₀ (𝑖 , 𝑖)} {f g : ⟨ M ⟩} where
  instance
    isSubsetoid:CoeqSolutions : isSubsetoid (CoeqSolutions f g)
    isSubsetoid.transp-Subsetoid isSubsetoid:CoeqSolutions (p) (incl P) = incl ((refl ≀⋆≀ p ⁻¹) ∙ P ∙ (refl ≀⋆≀ p))

  instance
    isIdeal-r:CoeqSolutions : isIdeal-r M ′(CoeqSolutions f g)′
    isIdeal-r.ideal-r-⋆ isIdeal-r:CoeqSolutions {h} (incl P) i =
      let P₀ : f ⋆ (h ⋆ i) ∼ g ⋆ (h ⋆ i)
          P₀ = f ⋆ (h ⋆ i)   ⟨ assoc-r-⋆ ⟩-∼
                (f ⋆ h) ⋆ i   ⟨ P ≀⋆≀ refl ⟩-∼
                (g ⋆ h) ⋆ i   ⟨ assoc-l-⋆ ⟩-∼
                g ⋆ (h ⋆ i)   ∎
      in incl P₀
    isIdeal-r.ideal-◍ isIdeal-r:CoeqSolutions = incl (absorb-r-⋆ ∙ absorb-r-⋆ ⁻¹)
-- private
module _ {𝒞 : 𝒰 𝑗} {{_ : isCategory {𝑖} 𝒞}} where
  Pair : (a b : 𝒞) -> 𝒰 _
  Pair a x = Hom a x ×-𝒰 Hom a x

IxC : (𝒞 : Category 𝑖) -> 𝒰 _
IxC 𝒞 = ∑ λ (a : ⟨ 𝒞 ⟩) -> ∑ λ b -> Pair a b

module _ (𝒞 : Category 𝑖) {{_ : isDiscrete ⟨ 𝒞 ⟩}} {{_ : isSet-Str ⟨ 𝒞 ⟩}} where
  𝓘C : (i : IxC 𝒞) -> Ideal-r ′(PathMon 𝒞)′
  𝓘C (_ , _ , f , g) = ′ (CoeqSolutions (arrow f) (arrow g)) ′

-- module _ {𝒞 : 𝒰 𝑖} {{_ : isCategory {𝑘} 𝒞}} {{_ : isDiscrete 𝒞}} {{_ : isSet-Str 𝒞}} where
  -- data isPrincipalC {a b : 𝒞} (f g : a ⟶ b) : 𝒰 𝑖 where
  --   solved : hasCoequalizer f g
  --   field princobj : 




module _ (𝒞 : SizedCategory 𝑖) where
  record isSplittableC (n : 人ℕ) {a b : ⟨ 𝒞 ⟩} (f : (a ⟶ b) ^ 2) : 𝒰 𝑖 where
    field famC : n ∍ tt -> ∑ λ a' -> (Pair a' b)
    field coversC : ∀{x} -> (h : b ⟶ x) -> (f ⌄ 0 ◆ h ∼ f ⌄ 1 ◆ h) ↔ (∀ p -> (famC p .snd) ⌄ 0 ◆ h ∼ (famC p .snd) ⌄ 1 ◆ h)
    -- field coversC : ⋀-fin (λ i -> 𝓘C 𝒞 (famC i)) ∼ 𝓘C 𝒞 i
    field fampropsC : ∀ k -> sizeC (famC k .snd) ≪ sizeC f
    -- P (_ , _ , f) (_ , _ , famC k .snd)
  open isSplittableC public

record isPrincipalFamilyCat (𝒞 : SizedCategory 𝑖) : 𝒰 (𝑖 ⁺) where
  field isBase : ∀{a x : ⟨ 𝒞 ⟩} -> (Pair a x) -> 𝒰 (𝑖 ⌄ 1)
  field ∂C : ∀{x y : ⟨ 𝒞 ⟩} -> (i : Pair x y)
           -> (isBase i +-𝒰 (∑ λ n -> isSplittableC 𝒞 n i))
  field isPrincipalC:Base : ∀{a b : ⟨ 𝒞 ⟩} -> ∀(f g : a ⟶ b) -> isBase (f , g) -> ¬ (hasCoequalizer f g) +-𝒰 (hasReducingCoequalizer f g)

open isPrincipalFamilyCat {{...}} public
