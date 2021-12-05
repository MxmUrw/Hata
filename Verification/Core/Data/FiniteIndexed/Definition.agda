
module Verification.Core.Data.FiniteIndexed.Definition where

open import Verification.Core.Conventions hiding (_⊔_)

open import Verification.Core.Set.Setoid.Definition
open import Verification.Core.Set.Set.Definition
open import Verification.Core.Set.Contradiction
-- open import Verification.Core.Set.Set.Instance.Category
open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Category.Std.Functor.Definition
open import Verification.Core.Category.Std.Morphism.Iso
open import Verification.Core.Category.Std.Morphism.EpiMono
open import Verification.Core.Category.Std.Functor.Image
open import Verification.Core.Category.Std.Functor.Adjoint
open import Verification.Core.Category.Std.Category.Structured.SeparatingFamily

open import Verification.Core.Data.Universe.Definition
open import Verification.Core.Data.Universe.Definition
open import Verification.Core.Data.Universe.Instance.Category
open import Verification.Core.Data.Universe.Instance.FiniteCoproductCategory
open import Verification.Core.Data.Universe.Instance.SeparatingFamily

open import Verification.Core.Data.Indexed.Definition
open import Verification.Core.Data.Indexed.Xiix
open import Verification.Core.Data.Indexed.Instance.Monoid
open import Verification.Core.Data.Indexed.Instance.FiniteCoproductCategory
open import Verification.Core.Data.Indexed.Instance.SeparatingFamily

open import Verification.Core.Algebra.Monoid.Definition
open import Verification.Core.Algebra.Monoid.Free
open import Verification.Core.Data.List.Variant.Binary.Instance.Monoid
open import Verification.Core.Data.List.Variant.Binary.Element.Definition
open import Verification.Core.Data.List.Variant.Binary.Element.As.Indexed

open import Verification.Core.Category.Std.Category.Subcategory.Full
open import Verification.Core.Category.Std.Limit.Specific.Coproduct.Definition
open import Verification.Core.Category.Std.Limit.Specific.Coproduct.Preservation.Definition
open import Verification.Core.Category.Std.Category.Subcategory.Full.Construction.Coproduct

module _ (I : 𝒰 𝑖) where

  FiniteIndexed : 𝒰 _
  FiniteIndexed = 𝐅𝐮𝐥𝐥 (𝐈𝐱 I (𝐔𝐧𝐢𝐯 𝑖)) 𝑒𝑙

  macro 𝐅𝐢𝐧𝐈𝐱 = #structureOn FiniteIndexed



module _ {I : 𝒰 𝑖} where

  ι-𝐅𝐢𝐧𝐈𝐱ᵘ : 𝐅𝐢𝐧𝐈𝐱 I -> 𝐈𝐱 I (𝐔𝐧𝐢𝐯 𝑖)
  ι-𝐅𝐢𝐧𝐈𝐱ᵘ = 𝑓𝑢𝑙𝑙 (𝐈𝐱 I (𝐔𝐧𝐢𝐯 𝑖)) 𝑒𝑙

  macro ι-𝐅𝐢𝐧𝐈𝐱 = #structureOn ι-𝐅𝐢𝐧𝐈𝐱ᵘ

  instance
    hasInclusion:𝐅𝐢𝐧𝐈𝐱,𝐈𝐱 : hasInclusion (𝐅𝐢𝐧𝐈𝐱 I) (𝐈𝐱 I (𝐔𝐧𝐢𝐯 𝑖))
    hasInclusion:𝐅𝐢𝐧𝐈𝐱,𝐈𝐱 = inclusion ι-𝐅𝐢𝐧𝐈𝐱

  private
    F : Functor _ _
    F = (𝑓𝑢𝑙𝑙 (𝐈𝐱 I (𝐔𝐧𝐢𝐯 𝑖)) 𝑒𝑙)

  _⊔-𝐅𝐢𝐧𝐈𝐱_ : (a b : 𝐅𝐢𝐧𝐈𝐱 I) -> 𝐅𝐢𝐧𝐈𝐱 I
  _⊔-𝐅𝐢𝐧𝐈𝐱_ a b = (incl (⟨ a ⟩ ⋆ ⟨ b ⟩))

  module _ {a b : 𝐅𝐢𝐧𝐈𝐱 I} where
    private

      lem-1 : isCoproduct (𝑒𝑙 ⟨ a ⟩) (𝑒𝑙 ⟨ b ⟩) (𝑒𝑙 ⟨ a ⟩ ⊔ 𝑒𝑙 ⟨ b ⟩)
      lem-1 = it

      lem-2 : ∀{a b : 𝐅𝐢𝐧𝐈𝐱 I} -> (𝑒𝑙 ⟨ a ⟩ ⊔ 𝑒𝑙 ⟨ b ⟩) ≅ (𝑒𝑙 (⟨ a ⟩ ⋆ ⟨ b ⟩))
      lem-2 = pres-⋆ ⁻¹

      lem-3 : isCoproduct (𝑒𝑙 ⟨ a ⟩) (𝑒𝑙 ⟨ b ⟩) (𝑒𝑙 (⟨ a ⟩ ⋆ ⟨ b ⟩))
      lem-3 = transp-≅-Coproduct lem-2 {{lem-1}}

    instance
      isCoproduct:⊔-𝐅𝐢𝐧𝐈𝐱 : isCoproduct a b (a ⊔-𝐅𝐢𝐧𝐈𝐱 b)
      isCoproduct:⊔-𝐅𝐢𝐧𝐈𝐱 = isCoproduct:byFullSubcategory {{lem-3}}

    instance
      preservesCoproduct:𝑓𝑢𝑙𝑙-𝐅𝐢𝐧𝐈𝐱 : preservesCoproduct F a b (a ⊔-𝐅𝐢𝐧𝐈𝐱 b)
      preservesCoproduct.preserve-isCoproduct preservesCoproduct:𝑓𝑢𝑙𝑙-𝐅𝐢𝐧𝐈𝐱 = lem-3
      preservesCoproduct.preserve-ι₀ preservesCoproduct:𝑓𝑢𝑙𝑙-𝐅𝐢𝐧𝐈𝐱 = λ _ -> refl
      preservesCoproduct.preserve-ι₁ preservesCoproduct:𝑓𝑢𝑙𝑙-𝐅𝐢𝐧𝐈𝐱 = λ _ -> refl

  ⊥-𝐅𝐢𝐧𝐈𝐱 : 𝐅𝐢𝐧𝐈𝐱 I
  ⊥-𝐅𝐢𝐧𝐈𝐱 = incl ◌

  instance
    hasCoproducts:𝐅𝐢𝐧𝐈𝐱 : hasCoproducts (𝐅𝐢𝐧𝐈𝐱 I)
    hasCoproducts._⊔_ hasCoproducts:𝐅𝐢𝐧𝐈𝐱            = _⊔-𝐅𝐢𝐧𝐈𝐱_
    hasCoproducts.isCoproduct:⊔ hasCoproducts:𝐅𝐢𝐧𝐈𝐱  = isCoproduct:⊔-𝐅𝐢𝐧𝐈𝐱

  instance
    isInitial:⊥-𝐅𝐢𝐧𝐈𝐱 : isInitial ⊥-𝐅𝐢𝐧𝐈𝐱
    isInitial:⊥-𝐅𝐢𝐧𝐈𝐱 = record { elim-⊥ = incl (λ {i ()}) ; expand-⊥ = {!!} }

  instance
    hasInitial:𝐅𝐢𝐧𝐈𝐱 : hasInitial (𝐅𝐢𝐧𝐈𝐱 I)
    hasInitial.⊥ hasInitial:𝐅𝐢𝐧𝐈𝐱            = ⊥-𝐅𝐢𝐧𝐈𝐱
    hasInitial.isInitial:⊥ hasInitial:𝐅𝐢𝐧𝐈𝐱  = {!!}

  instance
    hasFiniteCoproducts:𝐅𝐢𝐧𝐈𝐱 : hasFiniteCoproducts (𝐅𝐢𝐧𝐈𝐱 I)
    hasFiniteCoproducts:𝐅𝐢𝐧𝐈𝐱 = hasFiniteCoproducts:default

  instance
    isFiniteCoproductPreserving:𝑓𝑢𝑙𝑙-𝐅𝐢𝐧𝐈𝐱 : isFiniteCoproductPreserving (𝑓𝑢𝑙𝑙 (𝐈𝐱 I (𝐔𝐧𝐢𝐯 𝑖)) 𝑒𝑙)
    isFiniteCoproductPreserving.preservesCoproducts:this isFiniteCoproductPreserving:𝑓𝑢𝑙𝑙-𝐅𝐢𝐧𝐈𝐱 = it
    isFiniteCoproductPreserving.preservesInitial:this    isFiniteCoproductPreserving:𝑓𝑢𝑙𝑙-𝐅𝐢𝐧𝐈𝐱 = {!!}

module _ {I : 𝒰 𝑖} {{DP : isDiscrete I}} where

  private
    lem-1 : ∀ (s : Separator {𝒞 = 𝐈𝐱 I (𝐔𝐧𝐢𝐯 𝑖)}) -> inEssentialImage (𝑓𝑢𝑙𝑙 (𝐈𝐱 I (𝐔𝐧𝐢𝐯 𝑖)) 𝑒𝑙) (separator s)
    lem-1 (s , i) = incl (incl i) , P

      where
        f : 𝑒𝑙 (incl i) ⟶ separator-𝐈𝐱 (s , i)
        f j x with i ≟-Str j
        ... | yes p = tt
        f j incl | no ¬p = impossible (¬p refl-≣)

        g : separator-𝐈𝐱 (s , i) ⟶ 𝑒𝑙 (incl i)
        g = free (λ x → incl)

        lem-1-10 : ∀{a : I} -> (p q : incl a ∍ a) -> p ≡ q
        lem-1-10 p q = {!!}

        lem-1-20 : f ◆ g ∼ id
        lem-1-20 j with i ≟-Str j
        ... | yes refl-≣ = funExt (λ _ -> lem-1-10 _ _)
        ... | no ¬p = funExt (λ x -> impossible (¬p (identify-∍ x)))

        lem-1-30 : g ◆ f ∼ id
        lem-1-30 j with i ≟-Str j
        ... | yes p = funExt λ {tt → refl-≡}
        ... | no ¬p = funExt λ ()

        P : 𝑒𝑙 (incl i) ≅ separator (s , i)
        P = f since record { inverse-◆ = g ; inv-r-◆ = lem-1-20 ; inv-l-◆ = lem-1-30 }

  instance
    isMonoPreserving:𝑓𝑢𝑙𝑙-𝐅𝐢𝐧𝐈𝐱 : isMonoPreserving (𝑓𝑢𝑙𝑙 (𝐈𝐱 I (𝐔𝐧𝐢𝐯 𝑖)) 𝑒𝑙)
    isMonoPreserving:𝑓𝑢𝑙𝑙-𝐅𝐢𝐧𝐈𝐱 = isMonoPreserving:byFullyFaithful lem-1


      -- where
      --   lem-1 : ∀ s -> inEssentialImage (𝑓𝑢𝑙𝑙 (𝐈𝐱 I (𝐔𝐧𝐢𝐯 𝑖)) 𝑒𝑙) (separator s)
      --   lem-1 (s , i) = incl (incl i) , P
      --     where
      --       f : 𝑒𝑙 (incl i) ⟶ sep (s , i)
      --       f {j} x with i ≟-Str j
      --       ... | no ¬p = {!!}
      --       ... | yes p with (DP isDiscrete.≟-Str i) j
      --       ... | Y = {!!}


      --       P : 𝑒𝑙 (incl i) ≅ separator (s , i)
      --       P = f since {!!}




