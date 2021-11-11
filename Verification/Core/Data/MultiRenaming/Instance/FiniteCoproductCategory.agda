
module Verification.Core.Data.MultiRenaming.Instance.FiniteCoproductCategory where

open import Verification.Conventions hiding (_⊔_)

open import Verification.Core.Set.Setoid.Definition
open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Category.Std.Functor.Definition
open import Verification.Core.Category.Std.Category.Instance.Category
open import Verification.Core.Category.Std.Functor.Instance.Category
open import Verification.Core.Category.Std.Natural.Definition
open import Verification.Core.Category.Std.Morphism.Iso
-- open import Verification.Core.Category.Std.Fibration.GrothendieckConstruction.Definition
open import Verification.Core.Category.Std.Fibration.GrothendieckConstruction.Op.Definition

open import Verification.Core.Algebra.Monoid.Definition
open import Verification.Core.Algebra.Monoid.Free
open import Verification.Core.Algebra.Monoid.Free.Element

open import Verification.Core.Data.Universe.Everything
open import Verification.Core.Data.FiniteIndexed.Definition
open import Verification.Core.Data.Indexed.Definition
open import Verification.Core.Data.Renaming.Definition
open import Verification.Core.Category.Std.Category.Subcategory.Full
open import Verification.Core.Category.Std.Category.Subcategory.Definition
open import Verification.Core.Category.Std.Morphism.EpiMono
open import Verification.Core.Category.Std.Category.Opposite
open import Verification.Core.Category.Std.Limit.Specific.Coproduct.Definition

open import Verification.Core.Data.MultiRenaming.Definition

-- x⃰ 
-- ⃩ 
-- ↑bar


-- b⃛ 	a⃜
-- b⃒ 	a⃓ b

-- ◌̂ 	x̃ 	x̄ 	a̅
-- a̰ 	x̱ 	a̲


module _ {K : 𝒰 𝑖} {L : 𝒰 𝑗} where
  infixl 70 _⊔-𝐌𝐮𝐥𝐭𝐢𝐑𝐞𝐧_

  private
    F : _ -> _
    F = multiren K L

    macro 𝐹 = #structureOn F

  private
    glue-⊔ : ∀{a b : 𝐅𝐢𝐧𝐈𝐱 K} -> (a⃩ : ⟨ 𝐹 a ⟩) (b⃩ : ⟨ 𝐹 b ⟩) -> ⟨ 𝐹 (a ⊔ b) ⟩
    glue-⊔ {a} {b} a⃩ b⃩ = indexed x
      where
        x : ∑ _∍_ ⟨ a ⊔ b ⟩ → (♮𝐑𝐞𝐧 L) ᵒᵖ⌯ᵘ
        x (i , right-∍ ip)  = ix b⃩ (i , ip)
        x (i , left-∍ ip)   = ix a⃩ (i , ip)

    γ₀ : {a b : 𝐅𝐢𝐧𝐈𝐱 K} -> {a⃩ : ⟨ 𝐹 a ⟩} {b⃩ : ⟨ 𝐹 b ⟩} -> a⃩ ⟶ ⟨ map ι₀ ⟩ (glue-⊔ a⃩ b⃩)
    γ₀ = id

    γ₁ : {a b : 𝐅𝐢𝐧𝐈𝐱 K} -> {a⃩ : ⟨ 𝐹 a ⟩} {b⃩ : ⟨ 𝐹 b ⟩} -> b⃩ ⟶ ⟨ map ι₁ ⟩ (glue-⊔ a⃩ b⃩)
    γ₁ = id


  _⊔-𝐌𝐮𝐥𝐭𝐢𝐑𝐞𝐧_ : (a b : 𝐌𝐮𝐥𝐭𝐢𝐑𝐞𝐧 K L) -> 𝐌𝐮𝐥𝐭𝐢𝐑𝐞𝐧 K L
  _⊔-𝐌𝐮𝐥𝐭𝐢𝐑𝐞𝐧_ (a , a⃩) (b , b⃩) = a ⊔ b , glue-⊔ a⃩ b⃩

  module _ {a b : 𝐌𝐮𝐥𝐭𝐢𝐑𝐞𝐧 K L} where
    ι₀-𝐌𝐮𝐥𝐭𝐢𝐑𝐞𝐧 : a ⟶ a ⊔-𝐌𝐮𝐥𝐭𝐢𝐑𝐞𝐧 b
    ι₀-𝐌𝐮𝐥𝐭𝐢𝐑𝐞𝐧 = ι₀ , id

    ι₁-𝐌𝐮𝐥𝐭𝐢𝐑𝐞𝐧 : b ⟶ a ⊔-𝐌𝐮𝐥𝐭𝐢𝐑𝐞𝐧 b
    ι₁-𝐌𝐮𝐥𝐭𝐢𝐑𝐞𝐧 = ι₁ , id

    ⦗_⦘-𝐌𝐮𝐥𝐭𝐢𝐑𝐞𝐧 : ∀{c} -> (a ⟶ c ×-𝒰 b ⟶ c) → a ⊔-𝐌𝐮𝐥𝐭𝐢𝐑𝐞𝐧 b ⟶ c
    ⦗_⦘-𝐌𝐮𝐥𝐭𝐢𝐑𝐞𝐧 ((f , f⃩) , (g , g⃩)) = ⦗ f , g ⦘ , {!!}

    instance
      isCoproduct:⊔-𝐌𝐮𝐥𝐭𝐢𝐑𝐞𝐧 : isCoproduct a b (a ⊔-𝐌𝐮𝐥𝐭𝐢𝐑𝐞𝐧 b)
      isCoproduct.ι₀ isCoproduct:⊔-𝐌𝐮𝐥𝐭𝐢𝐑𝐞𝐧 = ι₀-𝐌𝐮𝐥𝐭𝐢𝐑𝐞𝐧
      isCoproduct.ι₁ isCoproduct:⊔-𝐌𝐮𝐥𝐭𝐢𝐑𝐞𝐧 = ι₁-𝐌𝐮𝐥𝐭𝐢𝐑𝐞𝐧
      isCoproduct.⦗ isCoproduct:⊔-𝐌𝐮𝐥𝐭𝐢𝐑𝐞𝐧 ⦘ = ⦗_⦘-𝐌𝐮𝐥𝐭𝐢𝐑𝐞𝐧
      isCoproduct.isSetoidHom:⦗⦘ isCoproduct:⊔-𝐌𝐮𝐥𝐭𝐢𝐑𝐞𝐧 = {!!}
      isCoproduct.reduce-ι₀ isCoproduct:⊔-𝐌𝐮𝐥𝐭𝐢𝐑𝐞𝐧 = {!!}
      isCoproduct.reduce-ι₁ isCoproduct:⊔-𝐌𝐮𝐥𝐭𝐢𝐑𝐞𝐧 = {!!}
      isCoproduct.expand-ι₀,ι₁ isCoproduct:⊔-𝐌𝐮𝐥𝐭𝐢𝐑𝐞𝐧 = {!!}


  instance
    hasCoproducts:𝐌𝐮𝐥𝐭𝐢𝐑𝐞𝐧 : hasCoproducts (𝐌𝐮𝐥𝐭𝐢𝐑𝐞𝐧 K L)
    hasCoproducts._⊔_ hasCoproducts:𝐌𝐮𝐥𝐭𝐢𝐑𝐞𝐧 = _⊔-𝐌𝐮𝐥𝐭𝐢𝐑𝐞𝐧_
    hasCoproducts.isCoproduct:⊔ hasCoproducts:𝐌𝐮𝐥𝐭𝐢𝐑𝐞𝐧 = isCoproduct:⊔-𝐌𝐮𝐥𝐭𝐢𝐑𝐞𝐧


  --------------------------------------------------
  -- initial object

  ⊥-𝐌𝐮𝐥𝐭𝐢𝐑𝐞𝐧 : 𝐌𝐮𝐥𝐭𝐢𝐑𝐞𝐧 K L
  ⊥-𝐌𝐮𝐥𝐭𝐢𝐑𝐞𝐧 = ⊥ , indexed (λ {(a , ())})

  instance
    isInitial:⊥-𝐌𝐮𝐥𝐭𝐢𝐑𝐞𝐧 : isInitial ⊥-𝐌𝐮𝐥𝐭𝐢𝐑𝐞𝐧
    isInitial:⊥-𝐌𝐮𝐥𝐭𝐢𝐑𝐞𝐧 = {!!}

  instance
    hasInitial:𝐌𝐮𝐥𝐭𝐢𝐑𝐞𝐧 : hasInitial (𝐌𝐮𝐥𝐭𝐢𝐑𝐞𝐧 K L)
    hasInitial.⊥ hasInitial:𝐌𝐮𝐥𝐭𝐢𝐑𝐞𝐧 = ⊥-𝐌𝐮𝐥𝐭𝐢𝐑𝐞𝐧
    hasInitial.isInitial:⊥ hasInitial:𝐌𝐮𝐥𝐭𝐢𝐑𝐞𝐧 = isInitial:⊥-𝐌𝐮𝐥𝐭𝐢𝐑𝐞𝐧

  instance
    hasFiniteCoproducts:𝐌𝐮𝐥𝐭𝐢𝐑𝐞𝐧 : hasFiniteCoproducts (𝐌𝐮𝐥𝐭𝐢𝐑𝐞𝐧 K L)
    hasFiniteCoproducts:𝐌𝐮𝐥𝐭𝐢𝐑𝐞𝐧 = hasFiniteCoproducts:default


