
-- {-# OPTIONS --overlapping-instances #-}

module Verification.Core.Algebra.Abelian.Definition where

open import Verification.Conventions

open import Verification.Core.Data.Prop.Everything
open import Verification.Core.Set.Setoid.Definition
open import Verification.Core.Algebra.Monoid.Definition
open import Verification.Core.Algebra.Group.Definition
open import Verification.Core.Algebra.Group.Quotient


Abelian : (𝑗 : 𝔏 ^ 2) -> 𝒰 _
Abelian 𝑗 = Monoid 𝑗 :& (isGroup :, isCommutative)

-- Subabelian : (A : Abelian 𝑗) -> 𝒰 _
-- Subabelian A = Subgroup ′ ⟨ A ⟩ ′

-- record isSubabelian {A} {{_ : Abelian 𝑗 on A}} (P : 𝒫 A :& isSubsetoid :& isSubmonoid :& isSubgroup) : 𝒰 𝑗 where
record isSubabelian {𝑗 : 𝔏 ^ 2} {A : Abelian 𝑗} (P : 𝒫 ⟨ A ⟩ :& isSubsetoid :& isSubmonoid :& isSubgroup) : 𝒰 𝑗 where
open isSubabelian {{...}} public


Subabelian : {𝑗 : 𝔏 ^ 2} (A : Abelian 𝑗) -> 𝒰 _
Subabelian A = Subgroup ′ ⟨ A ⟩ ′ :& isSubabelian {A = A}


-- module _ {A : Abelian 𝑗} where
--   RelSubabelian : Subabelian A -> ⟨ A ⟩ -> ⟨ A ⟩ -> 𝒰 _
--   RelSubabelian B = RelSubgroup ′ ⟨ B ⟩ ′

-- RelSubabelian : {A : Abelian 𝑗} (B : Subabelian A) -> 

-- module _ {A : 𝒰 _} {B : 𝒫 A} {{_ : Abelian 𝑗 on A}} {{_ : Subgroup ′ A ′ on B}} where

--   instance
--     isNormal:Subabelian : isNormal ′ B ′
--     isNormal.normal isNormal:Subabelian a {b} b∈B =
--       let P₀ = b             ≣⟨ unit-r-⋆ ⁻¹ ⟩
--                 b ⋆ ◌         ≣⟨ refl `cong-⋆` inv-r-⋆ ⁻¹ ⟩
--                 b ⋆ (a ⋆ ◡ a) ≣⟨ assoc-r-⋆ ⟩
--                 b ⋆ a ⋆ ◡ a   ≣⟨ comm-⋆ `cong-⋆` refl ⟩
--                 a ⋆ b ⋆ ◡ a   ∎

--           P₁ : B (a ⋆ b ⋆ ◡ a)
--           P₁ = transp-Subsetoid P₀ b∈B
--       in P₁

-- private
module _ {𝑗 : 𝔏 ^ 2} {A : Group 𝑗} {B : Subgroup A} {{_ : isCommutative ′ ⟨ A ⟩ ′}} where
  instance
    isNormal:Subabelian : isNormal ′ ⟨ B ⟩ ′
    isNormal.normal isNormal:Subabelian a {b} b∈B =
      let P₀ = b             ≣⟨ unit-r-⋆ ⁻¹ ⟩
                b ⋆ ◌         ≣⟨ refl `cong-⋆` inv-r-⋆ ⁻¹ ⟩
                b ⋆ (a ⋆ ◡ a) ≣⟨ assoc-r-⋆ ⟩
                b ⋆ a ⋆ ◡ a   ≣⟨ comm-⋆ `cong-⋆` refl ⟩
                a ⋆ b ⋆ ◡ a   ∎

          P₁ : ⟨ ⟨ B ⟩ (a ⋆ b ⋆ ◡ a) ⟩
          P₁ = transp-Subsetoid P₀ b∈B
      in P₁

-- module _ {A : Abelian 𝑗} {B : Subabelian A} where
-- module _ {A : 𝒰 _} {B : 𝒫 A} {{_ : Abelian 𝑗 on A}} {{_ : Subabelian ′ A ′ on B}} where
-- module _ {A : Abelian 𝑗} {B : Subgroup ′ ⟨ A ⟩ ′} where
module _ {𝑗 : 𝔏 ^ 2} {A : Group 𝑗} {{_ : isCommutative ′ ⟨ A ⟩ ′}} {B : Subgroup A} where

  instance
    isCommutative:AbelianQuot : isCommutative (′ ⟨ ′ ⟨ A ⟩ ′ /-Group ′ ⟨ B ⟩ ′ ⟩ ′)
    -- isCommutative:AbelianQuot = {!!}
    isCommutative.comm-⋆ isCommutative:AbelianQuot {a = [ a ]} {b = [ b ]} = cong-∼ comm-⋆

  -- _/-Abelian_ : Abelian _
  -- _/-Abelian_ = ′ ⟨ ′ A ′ /-Group ′ B ′ ⟩ ′

-- RelSubabelian : {G : Abelian 𝑗} (H : Subabelian G) (a : ⟨ G ⟩) (b : ⟨ G ⟩) : 𝒰 (𝑗 ⌄ 0) where

_/-Abelian_ : {𝑗 : 𝔏 ^ 2} (A : Abelian 𝑗) -> (B : Subabelian A) -> Abelian _
-- _/-Abelian_ A B = ′ ⟨ ′ ⟨ A ⟩ ′ /-Group ′ ⟨ B ⟩ ′ ⟩ ′
_/-Abelian_ A B = ′ ⟨ A ⟩ /-𝒰 RelSubgroup ′ ⟨ B ⟩ ′ ′

  -- let XX : isCommutative ′ ⟨ A ⟩ ′
  --     XX = it
  --     YY = ⟨ A ⟩ /-𝒰 RelSubgroup ′ ⟨ B ⟩ ′
  --     -- YY1 : Monoid _ on YY
  --     -- YY1 = make∑i {_} {{isMonoid:GroupQuot {G = ′ ⟨ A ⟩ ′} {{isNormal:Subabelian {A = A}}}}}
  -- in ′ YY ′

-- _/-Abelian_ A B = ′ ⟨ A ⟩ /-𝒰 RelSubgroup ′ ⟨ B ⟩ ′ ′


-- ′ ⟨ ′ ⟨ A ⟩ ′ /-Group B ⟩ ′

{-
  -}
{-
  -- testaa : (a b : ⟨ ′ ⟨ A ⟩ ′ /-Group B ⟩) -> 𝟙-𝒰
  -- testaa a b =
  --   let x = a ⋆ b
  --   in {!!}

  -- instance
  --   open _:&_ (′ ⟨ A ⟩ ′ /-Group B)



-}

