
module Verification.Experimental.Data.MultiRenaming.Definition where

open import Verification.Conventions

open import Verification.Experimental.Set.Setoid.Definition
open import Verification.Experimental.Category.Std.Category.Definition
open import Verification.Experimental.Category.Std.Functor.Definition
open import Verification.Experimental.Category.Std.Category.Instance.Category
open import Verification.Experimental.Category.Std.Functor.Instance.Category
open import Verification.Experimental.Category.Std.Natural.Definition
open import Verification.Experimental.Category.Std.Morphism.Iso
-- open import Verification.Experimental.Category.Std.Fibration.GrothendieckConstruction.Definition
open import Verification.Experimental.Category.Std.Fibration.GrothendieckConstruction.Op.Definition

open import Verification.Experimental.Algebra.Monoid.Definition
open import Verification.Experimental.Algebra.Monoid.Free
open import Verification.Experimental.Algebra.Monoid.Free.Element

open import Verification.Experimental.Data.Universe.Everything
open import Verification.Experimental.Data.FiniteIndexed.Definition
open import Verification.Experimental.Data.Indexed.Definition
open import Verification.Experimental.Data.Renaming.Definition
open import Verification.Experimental.Category.Std.Category.Subcategory.Full
open import Verification.Experimental.Category.Std.Category.Subcategory.Definition
open import Verification.Experimental.Category.Std.Morphism.EpiMono
open import Verification.Experimental.Category.Std.Category.Opposite


module _ {K : 𝒰 𝑖} {L : 𝒰 𝑗} where

  ℛ : 𝒰 _
  ℛ = ♮𝐑𝐞𝐧 L

  multiren : 𝐅𝐢𝐧𝐈𝐱 K -> 𝐂𝐚𝐭 _
  multiren a = 𝐈𝐱 (∑ (⟨ a ⟩ ∍_)) (ℛ ᵒᵖ⌯)
  macro 𝑚𝑢𝑙𝑡𝑖𝑟𝑒𝑛 = #structureOn multiren

  map-𝑚𝑢𝑙𝑡𝑖𝑟𝑒𝑛 : ∀{a b : 𝐅𝐢𝐧𝐈𝐱 K} -> (f : b ⟶ a) -> Functor (𝑚𝑢𝑙𝑡𝑖𝑟𝑒𝑛 a) (𝑚𝑢𝑙𝑡𝑖𝑟𝑒𝑛 b)
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
    isFunctor:𝑚𝑢𝑙𝑡𝑖𝑟𝑒𝑛 : isFunctor (𝐅𝐢𝐧𝐈𝐱 K ᵒᵖ) (𝐂𝐚𝐭 _) 𝑚𝑢𝑙𝑡𝑖𝑟𝑒𝑛
    isFunctor.map isFunctor:𝑚𝑢𝑙𝑡𝑖𝑟𝑒𝑛 = map-𝑚𝑢𝑙𝑡𝑖𝑟𝑒𝑛
    isFunctor.isSetoidHom:map isFunctor:𝑚𝑢𝑙𝑡𝑖𝑟𝑒𝑛 = {!!}
    isFunctor.functoriality-id isFunctor:𝑚𝑢𝑙𝑡𝑖𝑟𝑒𝑛 = {!!}
    isFunctor.functoriality-◆ isFunctor:𝑚𝑢𝑙𝑡𝑖𝑟𝑒𝑛 = {!!}

module _ (K : 𝒰 𝑖) (L : 𝒰 𝑗) where
  MultiRen = ⨊ᵒᵖ (𝑚𝑢𝑙𝑡𝑖𝑟𝑒𝑛 {K = K} {L = L})
  macro 𝐌𝐮𝐥𝐭𝐢𝐑𝐞𝐧 = #structureOn MultiRen






-- module _ {K : 𝒰 𝑖} {L : 𝒰 𝑗} where

--   multiren : 𝐅𝐢𝐧𝐈𝐱 K -> 𝐂𝐚𝐭 _
--   multiren a = 𝐈𝐱 (∑ (⟨ a ⟩ ∍_)) (♮𝐑𝐞𝐧 L)
--   macro 𝑚𝑢𝑙𝑡𝑖𝑟𝑒𝑛 = #structureOn multiren

--   map-𝑚𝑢𝑙𝑡𝑖𝑟𝑒𝑛 : ∀{a b : 𝐅𝐢𝐧𝐈𝐱 K} -> (f : b ⟶ a) -> Functor (𝑚𝑢𝑙𝑡𝑖𝑟𝑒𝑛 a) (𝑚𝑢𝑙𝑡𝑖𝑟𝑒𝑛 b)
--   map-𝑚𝑢𝑙𝑡𝑖𝑟𝑒𝑛 {a} {b} f = F since isFunctor:F
--     where
--       F : 𝐈𝐱 (∑ (⟨ a ⟩ ∍_)) (♮𝐑𝐞𝐧 L) -> 𝐈𝐱 (∑ (⟨ b ⟩ ∍_)) (♮𝐑𝐞𝐧 L)
--       F x = indexed λ (k , kp) → ix x (k , map f k kp)

--       map-F : ∀{x y : 𝐈𝐱 (∑ (⟨ a ⟩ ∍_)) (♮𝐑𝐞𝐧 L)} -> (g : x ⟶ y) -> F x ⟶ F y
--       map-F {x} {y} g = λ i → g _

--       isFunctor:F : isFunctor _ _ F
--       isFunctor.map isFunctor:F = map-F
--       isFunctor.isSetoidHom:map isFunctor:F = {!!}
--       isFunctor.functoriality-id isFunctor:F = {!!}
--       isFunctor.functoriality-◆ isFunctor:F = {!!}

--   instance
--     isFunctor:𝑚𝑢𝑙𝑡𝑖𝑟𝑒𝑛 : isFunctor (𝐅𝐢𝐧𝐈𝐱 K ᵒᵖ) (𝐂𝐚𝐭 _) 𝑚𝑢𝑙𝑡𝑖𝑟𝑒𝑛
--     isFunctor.map isFunctor:𝑚𝑢𝑙𝑡𝑖𝑟𝑒𝑛 = map-𝑚𝑢𝑙𝑡𝑖𝑟𝑒𝑛
--     isFunctor.isSetoidHom:map isFunctor:𝑚𝑢𝑙𝑡𝑖𝑟𝑒𝑛 = {!!}
--     isFunctor.functoriality-id isFunctor:𝑚𝑢𝑙𝑡𝑖𝑟𝑒𝑛 = {!!}
--     isFunctor.functoriality-◆ isFunctor:𝑚𝑢𝑙𝑡𝑖𝑟𝑒𝑛 = {!!}

-- module _ (K : 𝒰 𝑖) (L : 𝒰 𝑗) where
--   MultiRen = ⨊ (𝑚𝑢𝑙𝑡𝑖𝑟𝑒𝑛 {K = K} {L = L})
--   macro 𝐌𝐮𝐥𝐭𝐢𝐑𝐞𝐧 = #structureOn MultiRen



