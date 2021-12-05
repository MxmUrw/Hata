
module Verification.Core.Data.MultiRenaming.Definition where

open import Verification.Conventions

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
open import Verification.Core.Data.List.Variant.Binary.Element

open import Verification.Core.Data.Universe.Definition
open import Verification.Core.Data.Universe.Instance.Category
open import Verification.Core.Data.FiniteIndexed.Definition
open import Verification.Core.Data.Indexed.Definition
open import Verification.Core.Data.Renaming.Definition
open import Verification.Core.Category.Std.Category.Subcategory.Full
open import Verification.Core.Category.Std.Category.Subcategory.Definition
open import Verification.Core.Category.Std.Morphism.EpiMono
open import Verification.Core.Category.Std.Category.Opposite



module _ (K : 𝒰 𝑖) (L : 𝒰 𝑗) where
  multiren : 𝐅𝐢𝐧𝐈𝐱 K -> 𝐂𝐚𝐭 _
  multiren a = 𝐈𝐱 (∑ (⟨ a ⟩ ∍_)) ′(♮𝐑𝐞𝐧 L ᵒᵖ⌯ᵘ)′
  macro 𝑚𝑢𝑙𝑡𝑖𝑟𝑒𝑛 = #structureOn multiren

module _ {K : 𝒰 𝑖} {L : 𝒰 𝑗} where
  private
    ℛ : 𝒰 _
    ℛ = ♮𝐑𝐞𝐧 L

  map-𝑚𝑢𝑙𝑡𝑖𝑟𝑒𝑛 : ∀{a b : 𝐅𝐢𝐧𝐈𝐱 K} -> (f : b ⟶ a) -> Functor (𝑚𝑢𝑙𝑡𝑖𝑟𝑒𝑛 K L a) (𝑚𝑢𝑙𝑡𝑖𝑟𝑒𝑛 K L b)
  map-𝑚𝑢𝑙𝑡𝑖𝑟𝑒𝑛 {a} {b} f = F since isFunctor:F
    where
      F : 𝐈𝐱 (∑ (⟨ a ⟩ ∍_)) (ℛ ᵒᵖ⌯) -> 𝐈𝐱 (∑ (⟨ b ⟩ ∍_)) (ℛ ᵒᵖ⌯)
      F x = indexed λ (k , kp) → ix x (k , map f k kp)

      map-F : ∀{x y : 𝐈𝐱 (∑ (⟨ a ⟩ ∍_)) (ℛ ᵒᵖ⌯)} -> (g : x ⟶ y) -> F x ⟶ F y
      map-F {x} {y} g = λ i → g _

      isFunctor:F : isFunctor _ _ F
      isFunctor.map isFunctor:F = map-F
      isFunctor.isSetoidHom:map isFunctor:F = {!!}
      isFunctor.functoriality-id isFunctor:F = {!!}
      isFunctor.functoriality-◆ isFunctor:F = {!!}

  instance
    isFunctor:𝑚𝑢𝑙𝑡𝑖𝑟𝑒𝑛 : isFunctor (𝐅𝐢𝐧𝐈𝐱 K ᵒᵖ) (𝐂𝐚𝐭 _) (𝑚𝑢𝑙𝑡𝑖𝑟𝑒𝑛 K L)
    isFunctor.map isFunctor:𝑚𝑢𝑙𝑡𝑖𝑟𝑒𝑛 = map-𝑚𝑢𝑙𝑡𝑖𝑟𝑒𝑛
    isFunctor.isSetoidHom:map isFunctor:𝑚𝑢𝑙𝑡𝑖𝑟𝑒𝑛 = {!!}
    isFunctor.functoriality-id isFunctor:𝑚𝑢𝑙𝑡𝑖𝑟𝑒𝑛 = {!!}
    isFunctor.functoriality-◆ isFunctor:𝑚𝑢𝑙𝑡𝑖𝑟𝑒𝑛 = {!!}

module _ (K : 𝒰 𝑖) (L : 𝒰 𝑗) where
  MultiRen = ⨊ᵒᵖᵘ (𝑚𝑢𝑙𝑡𝑖𝑟𝑒𝑛 K L)
  macro 𝐌𝐮𝐥𝐭𝐢𝐑𝐞𝐧 = #structureOn MultiRen


-- | The category 𝐌𝐮𝐥𝐭𝐢𝐑𝐞𝐧 has coproducts.
--   Actually, one could show this by showing that the functor |𝑚𝑢𝑙𝑡𝑖𝑟𝑒𝑛 : 𝐅𝐢𝐧𝐈𝐱 ⟶ 𝐂𝐚𝐭|,
--   seen as the fibration |⨊ 𝑚𝑢𝑙𝑡𝑖𝑟𝑒𝑛 ⟶ 𝐅𝐢𝐧𝐈𝐱| is a stack/2-sheaf
--   since it seems that stacks inherit the coproducts from their base category, i.e., 𝐅𝐢𝐧𝐈𝐱.
--
--   For basics on stacks see http://homepage.sns.it/vistoli/descent.pdf .





