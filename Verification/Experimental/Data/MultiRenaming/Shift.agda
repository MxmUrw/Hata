
module Verification.Experimental.Data.MultiRenaming.Shift where

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
open import Verification.Experimental.Category.Std.Fibration.GrothendieckConstruction.Op.Instance.Functor

open import Verification.Experimental.Algebra.Monoid.Definition
open import Verification.Experimental.Algebra.Monoid.Free
open import Verification.Experimental.Algebra.Monoid.Free.Element

open import Verification.Experimental.Data.Nat.Free
open import Verification.Experimental.Data.Universe.Everything
open import Verification.Experimental.Data.FiniteIndexed.Definition
open import Verification.Experimental.Data.Indexed.Definition
open import Verification.Experimental.Data.Indexed.Duplicate
open import Verification.Experimental.Data.Indexed.LiftFunctor
open import Verification.Experimental.Data.Renaming.Definition
open import Verification.Experimental.Data.Renaming.Shift
open import Verification.Experimental.Data.Renaming.Instance.CoproductMonoidal
open import Verification.Experimental.Category.Std.Category.Subcategory.Full
open import Verification.Experimental.Category.Std.Category.Subcategory.Definition
open import Verification.Experimental.Category.Std.Morphism.EpiMono
open import Verification.Experimental.Category.Std.Category.Opposite
open import Verification.Experimental.Category.Std.Category.Opposite.LiftFunctor
open import Verification.Experimental.Category.Std.Category.Opposite.Instance.Monoid

open import Verification.Experimental.Data.MultiRenaming.Definition
open import Verification.Experimental.Data.MultiRenaming.Instance.FiniteCoproductCategory


module _ {K : 𝒰 𝑖} {L : 𝒰 𝑗} {{_ : isDiscrete L}} where

  shiftₗ-𝑚𝑢𝑙𝑡𝑖𝑟𝑒𝑛 : List L -> ∀{a} -> Functor (multiren K L a) (multiren K L a)
  shiftₗ-𝑚𝑢𝑙𝑡𝑖𝑟𝑒𝑛 x = liftFunctor-𝐈𝐱 (const (liftFunctor-ᵒᵖ⌯ (𝑠ℎ𝑖𝑓𝑡ₗ-♮𝐑𝐞𝐧 x)))

  module _ {x : List L} where
    instance
      isNatural:shiftₗ-𝑚𝑢𝑙𝑡𝑖𝑟𝑒𝑛 : isNatural (𝑚𝑢𝑙𝑡𝑖𝑟𝑒𝑛 K L) (𝑚𝑢𝑙𝑡𝑖𝑟𝑒𝑛 K L) (shiftₗ-𝑚𝑢𝑙𝑡𝑖𝑟𝑒𝑛 x)
      isNatural.naturality isNatural:shiftₗ-𝑚𝑢𝑙𝑡𝑖𝑟𝑒𝑛 = {!!}

  shiftₗ-𝐌𝐮𝐥𝐭𝐢𝐑𝐞𝐧 : List L -> Functor (𝐌𝐮𝐥𝐭𝐢𝐑𝐞𝐧 K L) (𝐌𝐮𝐥𝐭𝐢𝐑𝐞𝐧 K L)
  shiftₗ-𝐌𝐮𝐥𝐭𝐢𝐑𝐞𝐧 x = map-⨊ᵒᵖ' ′ shiftₗ-𝑚𝑢𝑙𝑡𝑖𝑟𝑒𝑛 x ′

  shiftₗ-𝐌𝐮𝐥𝐭𝐢𝐑𝐞𝐧' : ∀(as : 人List (List L)) -> Functor (𝐈𝐱 [ as ]ᶠ (𝐌𝐮𝐥𝐭𝐢𝐑𝐞𝐧 K L)) (𝐈𝐱 [ as ]ᶠ (𝐌𝐮𝐥𝐭𝐢𝐑𝐞𝐧 K L))
  shiftₗ-𝐌𝐮𝐥𝐭𝐢𝐑𝐞𝐧' (as) = liftFunctor-𝐈𝐱 (λ (a , p) → shiftₗ-𝐌𝐮𝐥𝐭𝐢𝐑𝐞𝐧 a)

  分 : ∀(as : 人List (List L)) -> Functor (𝐌𝐮𝐥𝐭𝐢𝐑𝐞𝐧 K L) (𝐌𝐮𝐥𝐭𝐢𝐑𝐞𝐧 K L)
  分 as = (写 ◆-𝐂𝐚𝐭 shiftₗ-𝐌𝐮𝐥𝐭𝐢𝐑𝐞𝐧' as) ◆-𝐂𝐚𝐭 ⨆ᶠ

  -- (shiftₗ-𝑚𝑢𝑙𝑡𝑖𝑟𝑒𝑛 x since isNatural:shiftₗ-𝑚𝑢𝑙𝑡𝑖𝑟𝑒𝑛 {x})
  -- map {{of ⨊ᵒᵖ (𝑚𝑢𝑙𝑡𝑖𝑟𝑒𝑛 K L)}} (shiftₗ-𝑚𝑢𝑙𝑡𝑖𝑟𝑒𝑛 x)




