
-- {-# OPTIONS --overlapping-instances #-}

module Verification.Experimental.Order.Frame where

open import Verification.Conventions
-- open import Verification.Core.Category.Definition
-- open import Verification.Core.Category.Instance.Set.Definition
open import Verification.Experimental.Order.Preorder
open import Verification.Experimental.Order.Lattice


data Test : 𝒰₀ where

record isFrame (A : Preorder 𝑖 :& (hasAllJoins :, hasFiniteMeets)) : 𝒰 (𝑖 ⁺) where
  field distribute-Frame : ∀{X} {F : X -> ⟨ A ⟩} {a} -> ⋁ F ∧ a ≚ ⋁ (λ x -> F x ∧ a)

Frame : ∀(𝑖) -> 𝒰 (𝑖 ⁺)
Frame 𝑖 = _ :& (isFrame {𝑖 = 𝑖})

-- mytest2 : ∀{A : 𝒰 𝑖}
--           {_ : Frame 𝑖 on A}
--           -> 𝟙-𝒰
-- mytest2 {𝑖} {A = A} =
--   let X : Frame 𝑖 on A
--       X = it
--   in tt

-- unquoteDecl Frame frame = #struct "Frame" (quote isFrame) "A" Frame frame

-- instance
--   backP : {UU : 𝒰 𝑖} {{U : hasU UU 𝑘 𝑙}} {P : UU -> 𝒰 𝑗} -> {a : getU U} -> {{p1 : getP U a}} -> {{_ : P (reconstruct U (a , p1))}} -> ∑i λ (p1 : getP U a) -> P (reconstruct U (a , p1))
--   backP = make∑i

-- ∑i λ () -> P (reconstruct U (a , p1))

-- mytest2 : ∀{A} {{_ : Preorder 𝑖 on A}} -> 𝟘-𝒰
-- mytest2 {A = A} =
--   let X : isFrame A
--       X = it
--   in ?

record isFrameHom {A B : 𝒰 𝑖} {{_ : Frame 𝑖 on A}} {{_ : Frame 𝑖 on B}}
  (f : (A -> B)
     :& isMonotone
     :& preservesAllJoins :, preservesFiniteMeets)

     : 𝒰 𝑖 where

FrameHom : ∀ (A B : 𝒰 𝑖) -> {_ : Frame 𝑖 on A} {_ : Frame 𝑖 on B} -> 𝒰 (𝑖 ⁺)
FrameHom A B = _ :& isFrameHom {A = A} {B = B}

isCategory:Frame : ICategory (Frame 𝑖) (𝑖 ⁺ , 𝑖)
ICategory.Hom isCategory:Frame A B = FrameHom (⟨ A ⟩) (⟨ B ⟩)
ICategory._≣_ isCategory:Frame f g = ⟨ f ⟩ ≡ ⟨ g ⟩
ICategory.IEquiv:≣ isCategory:Frame = {!!}
ICategory.id isCategory:Frame = {!!}
ICategory._◆_ isCategory:Frame = {!!}
ICategory.unit-l-◆ isCategory:Frame = {!!}
ICategory.unit-r-◆ isCategory:Frame = {!!}
ICategory.unit-2-◆ isCategory:Frame = {!!}
ICategory.assoc-l-◆ isCategory:Frame = {!!}
ICategory.assoc-r-◆ isCategory:Frame = {!!}
ICategory._◈_ isCategory:Frame = {!!}

-- record isFrameHom2 (A : Frame 𝑖)
--   (B : 𝒰 𝑗) {{_ : Frame 𝑗 on B}}
--   (f : (⟨ A ⟩ -> B) :& isMonotone :& isCompleteJoinPreserving) : 𝒰 (𝑖 ､ 𝑗) where



