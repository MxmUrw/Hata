
module Verification.Experimental.Data.FiniteIndexed.Definition where

open import Verification.Experimental.Conventions hiding (_⊔_)

open import Verification.Experimental.Set.Setoid.Definition
open import Verification.Experimental.Set.Set.Definition
open import Verification.Experimental.Set.Set.Instance.Category
open import Verification.Experimental.Category.Std.Category.Definition
open import Verification.Experimental.Category.Std.Functor.Definition
open import Verification.Experimental.Category.Std.Morphism.Iso
open import Verification.Experimental.Category.Std.Morphism.EpiMono
open import Verification.Experimental.Category.Std.Functor.Image
open import Verification.Experimental.Category.Std.Category.Structured.SeparatingFamily

open import Verification.Experimental.Data.Universe.Definition
open import Verification.Experimental.Data.Universe.Everything
open import Verification.Experimental.Data.Universe.Instance.FiniteCoproductCategory
open import Verification.Experimental.Data.Universe.Instance.SeparatingFamily

open import Verification.Experimental.Data.Indexed.Definition
open import Verification.Experimental.Data.Indexed.Instance.Monoid
open import Verification.Experimental.Data.Indexed.Instance.FiniteCoproductCategory
open import Verification.Experimental.Data.Indexed.Instance.SeparatingFamily

open import Verification.Experimental.Algebra.Monoid.Definition
open import Verification.Experimental.Algebra.Monoid.Free
open import Verification.Experimental.Algebra.Monoid.Free.Element

open import Verification.Experimental.Category.Std.Category.Subcategory.Full public
open import Verification.Experimental.Category.Std.Limit.Specific.Coproduct.Definition
open import Verification.Experimental.Category.Std.Category.Subcategory.Full.Construction.Coproduct

module _ (I : 𝒰 𝑖) where

  FiniteIndexed : 𝒰 _
  FiniteIndexed = 𝐅𝐮𝐥𝐥 (𝐈𝐱 I (𝐔𝐧𝐢𝐯 𝑖)) 𝑒𝑙

  macro 𝐅𝐢𝐧𝐈𝐱 = #structureOn FiniteIndexed


module _ {I : 𝒰 𝑖} where

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

  ⊥-𝐅𝐢𝐧𝐈𝐱 : 𝐅𝐢𝐧𝐈𝐱 I
  ⊥-𝐅𝐢𝐧𝐈𝐱 = incl ◌

  instance
    hasCoproducts:𝐅𝐢𝐧𝐈𝐱 : hasCoproducts (𝐅𝐢𝐧𝐈𝐱 I)
    hasCoproducts._⊔_ hasCoproducts:𝐅𝐢𝐧𝐈𝐱            = _⊔-𝐅𝐢𝐧𝐈𝐱_
    hasCoproducts.isCoproduct:⊔ hasCoproducts:𝐅𝐢𝐧𝐈𝐱  = isCoproduct:⊔-𝐅𝐢𝐧𝐈𝐱

  instance
    hasInitial:𝐅𝐢𝐧𝐈𝐱 : hasInitial (𝐅𝐢𝐧𝐈𝐱 I)
    hasInitial.⊥ hasInitial:𝐅𝐢𝐧𝐈𝐱            = ⊥-𝐅𝐢𝐧𝐈𝐱
    hasInitial.isInitial:⊥ hasInitial:𝐅𝐢𝐧𝐈𝐱  = record { elim-⊥ = {!!} ; expand-⊥ = {!!} }

  instance
    hasFiniteCoproducts:𝐅𝐢𝐧𝐈𝐱 : hasFiniteCoproducts (𝐅𝐢𝐧𝐈𝐱 I)
    hasFiniteCoproducts:𝐅𝐢𝐧𝐈𝐱 = hasFiniteCoproducts:default

module _ {I : 𝒰 𝑖} {{DP : isDiscrete I}} where

  lem-1 : ∀ (s : Separator {𝒞 = 𝐈𝐱 I (𝐔𝐧𝐢𝐯 𝑖)}) -> inEssentialImage (𝑓𝑢𝑙𝑙 (𝐈𝐱 I (𝐔𝐧𝐢𝐯 𝑖)) 𝑒𝑙) (separator s)
  lem-1 (s , i) = incl (incl i) , {!!} -- P

    -- where
    --   f : 𝑒𝑙 (incl i) ⟶ sep (s , i)
    --   f {j} x with i ≟-Str j
    --   ... | no ¬p = {!!}
    --   ... | yes p with (DP isDiscrete.≟-Str i) j
    --   ... | Y = {!!}


    --   P : 𝑒𝑙 (incl i) ≅ separator (s , i)
    --   P = f since {!!}

  -- instance
  --   isMonoPreserving:𝑓𝑢𝑙𝑙-𝐅𝐢𝐧𝐈𝐱 : isMonoPreserving (𝑓𝑢𝑙𝑙 (𝐈𝐱 I (𝐔𝐧𝐢𝐯 𝑖)) 𝑒𝑙)
  --   isMonoPreserving:𝑓𝑢𝑙𝑙-𝐅𝐢𝐧𝐈𝐱 = isMonoPreserving:byFullyFaithful lem-1
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




