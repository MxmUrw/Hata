
module Verification.Core.Category.Instance.IdxSet.Definition where

open import Verification.Conventions
open import Verification.Core.Category.Definition
open import Verification.Core.Category.Proper
open import Verification.Core.Homotopy.Level
open import Verification.Core.Category.Instance.Type


record IIdxSet (K : 𝒰 𝑖) {𝑗} (A : K -> 𝒰 𝑗) : 𝒰 (𝑖 ､ 𝑗) where
  field {{ISet:this}} : ∀{k : K} -> ISet (A k)
open IIdxSet {{...}} public
unquoteDecl IdxSet idxSet = #struct "IdxSt" (quote IIdxSet) "A" IdxSet idxSet

record IIdxSetHom {K : 𝒰 𝑘} (A : IdxSet K 𝑖) (B : IdxSet K 𝑗) (f : ∀{k : K} -> ⟨ A ⟩ k -> ⟨ B ⟩ k) : 𝒰 (𝑖 ､ 𝑗) where

instance
  IIdxSetHom:Anything : {K : 𝒰 𝑘} {A : IdxSet K 𝑖} {B : IdxSet K 𝑗} {f : ∀{k : K} -> ⟨ A ⟩ k -> ⟨ B ⟩ k} -> IIdxSetHom A B f
  IIdxSetHom:Anything = record {}

open IIdxSetHom {{...}} public
unquoteDecl IdxSetHom idxSetHom = #struct "IdxStHom" (quote IIdxSetHom) "f" IdxSetHom idxSetHom

module _ {K : 𝒰 𝑘} where
  record is-≣-IdxSet {A : IdxSet K 𝑖} {B : IdxSet K 𝑗} (f g : IdxSetHom A B) (P : ∀{k} x -> ⟨ f ⟩ {k} x ≡ ⟨ g ⟩ {k} x) : 𝒰 (𝑖 ､ 𝑗) where

  instance
    is-≣-IdxSet-Anything : {A : IdxSet K 𝑖} {B : IdxSet K 𝑗} {f g : IdxSetHom A B} {P : ∀{k} x -> ⟨ f ⟩ {k} x ≡ ⟨ g ⟩ {k} x} -> is-≣-IdxSet f g P
    is-≣-IdxSet-Anything = record {}


open is-≣-IdxSet {{...}} public
unquoteDecl _≣-IdxSet_ mk-≣-IdxSet = #struct "_≣_" (quote is-≣-IdxSet) "P" _≣-IdxSet_ mk-≣-IdxSet

module _ {K : 𝒰 𝑘} where
  instance
    isEquivRel:≣-IdxSet : {A : IdxSet K 𝑖} {B : IdxSet K 𝑗} -> isEquivRel (_≣-IdxSet_ {A = A} {B = B})
    ⟨ isEquivRel.refl isEquivRel:≣-IdxSet ⟩ _ = refl
    ⟨ isEquivRel.sym isEquivRel:≣-IdxSet p ⟩ x = ⟨ p ⟩ x ⁻¹
    ⟨ isEquivRel._∙_ isEquivRel:≣-IdxSet p q ⟩ x = ⟨ p ⟩ x ∙ ⟨ q ⟩ x

instance
  isEquivRel:≣-on-IdxSet : {K : 𝒰 𝑘} {A : IdxSet K 𝑖} {B : IdxSet K 𝑗} -> isEquivRel (λ (f g : IdxSetHom A B) -> ∀{k} -> ∀ x -> ⟨ f ⟩ {k} x ≡ ⟨ g ⟩ {k} x)
  isEquivRel.refl isEquivRel:≣-on-IdxSet x = refl
  isEquivRel.sym isEquivRel:≣-on-IdxSet p x₁ = p _ ⁻¹
  isEquivRel._∙_ isEquivRel:≣-on-IdxSet p q _ = p _ ∙ q _



Category:IdxSet : ∀(K : 𝒰 𝑘) -> ∀ 𝑖 -> Category (𝑖 ⁺ ⊔ 𝑘 , (𝑘 ⊔ 𝑖) , (𝑘 ⊔ 𝑖))
⟨ Category:IdxSet K 𝑖 ⟩ = IdxSet K 𝑖
isCategory.Hom (of Category:IdxSet K 𝑖) = IdxSetHom
isCategory._≣_ (of Category:IdxSet K 𝑖) f g = ∀{k} -> ∀ x -> ⟨ f ⟩ {k} x ≡ ⟨ g ⟩ {k} x
-- f ≣-IdxSet g -- 
-- ∀ {k} x -> ⟨ f ⟩ {k} x ≡ ⟨ g ⟩ {k} x
isCategory.isEquivRel:≣ (of Category:IdxSet K 𝑖) = isEquivRel:≣-on-IdxSet
isCategory.id (of Category:IdxSet K 𝑖) = idxSetHom (id)
isCategory._◆_ (of Category:IdxSet K 𝑖) f g = ` (λ {k} -> ⟨ f ⟩ {k} ◆ ⟨ g ⟩ {k}) `
isCategory.unit-l-◆ (of Category:IdxSet K 𝑖) = {!!}
isCategory.unit-r-◆ (of Category:IdxSet K 𝑖) = {!!}
isCategory.unit-2-◆ (of Category:IdxSet K 𝑖) = {!!}
isCategory.assoc-l-◆ (of Category:IdxSet K 𝑖) = {!!}
isCategory.assoc-r-◆ (of Category:IdxSet K 𝑖) = {!!}
isCategory._◈_ (of Category:IdxSet K 𝑖) = {!!}

instance isCategory:IdxSet = #openstruct Category:IdxSet

module _ {K : 𝒰 𝑘} where
  instance
    I1Category:IdxSet : I1Category (Category:IdxSet K 𝑗)
    I1Category:IdxSet = {!!}


