
module Verification.Experimental.Algebra.Group.Quotient where

open import Verification.Experimental.Conventions
open import Verification.Experimental.Meta.Structure
open import Verification.Experimental.Data.Prop.Everything
open import Verification.Experimental.Set.Setoid.Definition
open import Verification.Experimental.Algebra.Monoid.Definition
open import Verification.Experimental.Algebra.Group.Definition

module _ {𝑗 : 𝔏 ^ 2} {G : Group 𝑗} where
  record isNormal (H : Subgroup G) : 𝒰 𝑗 where
    field normal : ∀ a -> ∀{b : ⟨ G ⟩} -> ⟨ ⟨ H ⟩ b ⟩ -> ⟨ ⟨ H ⟩ (a ⋆ b ⋆ ◡ a) ⟩

  open isNormal {{...}} public

module _ where
-- private
  module _ {𝑗 : 𝔏 ^ 2} {G : Group 𝑗} {H : Subgroup G} {{_ : isNormal H}} where

    private
      lem-10 : ∀{a : ⟨ G ⟩} -> RelSubgroup H a a
      lem-10 {a} = incl (transp-Subsetoid (inv-r-⋆ ⁻¹) closed-◌)

      lem-20 : ∀{a b} -> RelSubgroup H a b -> RelSubgroup H b a
      lem-20 {a} {b} (incl x) =
        let p : ◡ (a ⋆ ◡ b) ∼ b ⋆ (◡ a)
            p = ◡ (a ⋆ ◡ b) ≣⟨ distr-⋆-◡ ⟩
                ◡ ◡ b ⋆ ◡ a ≣⟨ double-◡ `cong-⋆` refl ⟩
                b ⋆ ◡ a     ∎
        in incl (transp-Subsetoid p (closed-◡ x))

      lem-30 : ∀{a b c} -> RelSubgroup H a b -> RelSubgroup H b c -> RelSubgroup H a c
      lem-30 {a} {b} {c} (incl p) (incl q) =
        let P = (a ⋆ ◡ b) ⋆ (b ⋆ ◡ c) ≣⟨ assoc-r-⋆ ⟩
                (a ⋆ ◡ b) ⋆ b ⋆ ◡ c   ≣⟨ assoc-l-⋆ `cong-⋆` refl ⟩
                a ⋆ (◡ b ⋆ b) ⋆ ◡ c   ≣⟨ refl `cong-⋆` inv-l-⋆ `cong-⋆` refl ⟩
                a ⋆ ◌ ⋆ ◡ c           ≣⟨ unit-r-⋆ `cong-⋆` refl ⟩
                a ⋆ ◡ c               ∎
        in incl (transp-Subsetoid P (closed-⋆ p q))

    instance
      isEquivRel:RelSubgroup : isEquivRel (RelSubgroup H)
      isEquivRel.refl isEquivRel:RelSubgroup = lem-10
      isEquivRel.sym isEquivRel:RelSubgroup = lem-20
      isEquivRel._∙_ isEquivRel:RelSubgroup = lem-30

    instance
      isSetoidHom:[] : isSetoidHom ′(⟨ G ⟩)′ ′(⟨ G ⟩ /-𝒰 RelSubgroup H)′ [_]
      isSetoidHom.preserves-∼ isSetoidHom:[] {a} {b} (p) =
        let P = a ⋆ ◡ b ≣⟨ p `cong-⋆` refl ⟩
                b ⋆ ◡ b ≣⟨ inv-r-⋆ ⟩
                ◌       ∎
        in incl (incl (transp-Subsetoid (P ⁻¹) closed-◌))

    instance
      isMonoid:GroupQuot : isMonoid ′ ⟨ G ⟩ /-𝒰 RelSubgroup H ′
      isMonoid._⋆_ isMonoid:GroupQuot [ a ] [ b ] = [ a ⋆ b ]
      isMonoid.◌ isMonoid:GroupQuot = [ ◌ ]
      isMonoid.unit-l-⋆ isMonoid:GroupQuot {a = [ a ]} = preserves-∼ unit-l-⋆
      isMonoid.unit-r-⋆ isMonoid:GroupQuot {a = [ a ]} = preserves-∼ unit-r-⋆
      isMonoid.assoc-l-⋆ isMonoid:GroupQuot {a = [ a ]} {b = [ b ]} {c = [ c ]} = preserves-∼ assoc-l-⋆
      isMonoid.assoc-r-⋆ isMonoid:GroupQuot {a = [ a ]} {b = [ b ]} {c = [ c ]} = preserves-∼ assoc-r-⋆
      isMonoid._`cong-⋆`_ isMonoid:GroupQuot {a₀ = [ a₀ ]} {a₁ = [ a₁ ]} {b₀ = [ b₀ ]} {b₁ = [ b₁ ]} (incl (incl p)) (incl (incl q)) =
        let P₀ : ⟨ ⟨ H ⟩ (a₁ ⋆ (b₀ ⋆ ◡ b₁) ⋆ ◡ a₁) ⟩
            P₀ = normal a₁ q

            P₁ : ⟨ ⟨ H ⟩ ((a₀ ⋆ ◡ a₁) ⋆ (a₁ ⋆ (b₀ ⋆ ◡ b₁) ⋆ ◡ a₁)) ⟩
            P₁ = closed-⋆ p P₀

            P₂ = ((a₀ ⋆ ◡ a₁) ⋆ (a₁ ⋆ (b₀ ⋆ ◡ b₁) ⋆ ◡ a₁))  ≣⟨ assoc-l-⋆ ⟩
                (a₀ ⋆ (◡ a₁ ⋆ (a₁ ⋆ (b₀ ⋆ ◡ b₁) ⋆ ◡ a₁)))  ≣⟨ refl `cong-⋆` assoc-r-⋆ ⟩
                (a₀ ⋆ (◡ a₁ ⋆ (a₁ ⋆ (b₀ ⋆ ◡ b₁)) ⋆ ◡ a₁))  ≣⟨ refl `cong-⋆` (assoc-r-⋆ `cong-⋆` refl) ⟩
                (a₀ ⋆ ((◡ a₁ ⋆ a₁) ⋆ (b₀ ⋆ ◡ b₁) ⋆ ◡ a₁))  ≣⟨ refl `cong-⋆` ((inv-l-⋆ `cong-⋆` refl) `cong-⋆` refl) ⟩
                (a₀ ⋆ (◌ ⋆ (b₀ ⋆ ◡ b₁) ⋆ ◡ a₁))            ≣⟨ refl `cong-⋆` (unit-l-⋆ `cong-⋆` refl) ⟩
                (a₀ ⋆ ((b₀ ⋆ ◡ b₁) ⋆ ◡ a₁))                ≣⟨ refl `cong-⋆` assoc-l-⋆ ⟩
                (a₀ ⋆ (b₀ ⋆ (◡ b₁ ⋆ ◡ a₁)))                ≣⟨ assoc-r-⋆ ⟩
                ((a₀ ⋆ b₀) ⋆ (◡ b₁ ⋆ ◡ a₁))                ≣⟨ refl `cong-⋆` distr-⋆-◡ ⁻¹ ⟩
                (a₀ ⋆ b₀) ⋆ ◡ (a₁ ⋆ b₁)                    ∎

            P₃ : ⟨ ⟨ H ⟩ ((a₀ ⋆ b₀) ⋆ ◡ (a₁ ⋆ b₁)) ⟩
            P₃ = transp-Subsetoid P₂ P₁

        in incl (incl P₃)

    instance
      isGroup:GroupQuot : isGroup ′ ⟨ G ⟩ /-𝒰 RelSubgroup H ′
      isGroup.◡_ isGroup:GroupQuot [ a ] = [ ◡ a ]
      isGroup.inv-l-⋆ isGroup:GroupQuot {a = [ a ]} = preserves-∼ inv-l-⋆
      isGroup.inv-r-⋆ isGroup:GroupQuot {a = [ a ]} = preserves-∼ inv-r-⋆
      isGroup.cong-◡_ isGroup:GroupQuot {a₀ = [ a₀ ]} {a₁ = [ a₁ ]} (incl (incl p)) =
        let P₀ = ◡ (a₀ ⋆ ◡ a₁)               ≣⟨ distr-⋆-◡ ⟩
                  ◡ ◡ a₁ ⋆ ◡ a₀               ≣⟨ double-◡ `cong-⋆` refl ⟩
                  a₁ ⋆ ◡ a₀                   ∎

            P₁ : ⟨ ⟨ H ⟩ (a₁ ⋆ ◡ a₀) ⟩
            P₁ = transp-Subsetoid P₀ (closed-◡ p)

            P₂ : ⟨ ⟨ H ⟩ (◡ a₁ ⋆ (a₁ ⋆ ◡ a₀) ⋆ ◡ ◡ a₁) ⟩
            P₂ = normal (◡ a₁) P₁

            P₃ = ◡ a₁ ⋆ (a₁ ⋆ ◡ a₀) ⋆ ◡ ◡ a₁ ≣⟨ assoc-r-⋆ `cong-⋆` refl ⟩
                  (◡ a₁ ⋆ a₁) ⋆ ◡ a₀ ⋆ ◡ ◡ a₁ ≣⟨ inv-l-⋆ `cong-⋆` refl `cong-⋆` refl ⟩
                  ◌ ⋆ ◡ a₀ ⋆ ◡ ◡ a₁           ≣⟨ unit-l-⋆ `cong-⋆` refl ⟩
                  ◡ a₀ ⋆ ◡ ◡ a₁               ∎

            P₄ : ⟨ ⟨ H ⟩ (◡ a₀ ⋆ ◡ ◡ a₁) ⟩
            P₄ = transp-Subsetoid P₃ P₂
        in incl (incl P₄)

_/-Group_ : {𝑗 : 𝔏 ^ 2} (G : Group 𝑗) -> (H : Subgroup G) {{_ : isNormal H}} -> Group _
_/-Group_ G H = ′ ⟨ G ⟩ /-𝒰 RelSubgroup H ′

