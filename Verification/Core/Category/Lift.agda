
{-# OPTIONS --cubical --allow-unsolved-metas #-}

module Verification.Core.Category.Lift where

open import Verification.Conventions
open import Verification.Core.Category.Definition
open import Verification.Core.Algebra.Basic.Monoid
open import Verification.Core.Order.Instance.Product
open import Verification.Core.Order.Instance.Level
open import Verification.Core.Order.Lattice
-- open import Verification.Core.Category.Instance.Cat

--------------------------------------------------------------------
-- Universe level monoid / sup lattice




-- merge : 𝔏 ^ n -> 𝔏 ^ n -> 𝔏 ^ n
-- merge 

many : ∀{A : 𝒰 ℓ} -> A -> (A ^ n)
many {n = zero} a = ↥ tt
many {n = suc zero} a = a
many {n = suc (suc n)} a = a , many a

_∨-𝔏_ : 𝔏 ^ n -> 𝔏 ^ n -> 𝔏 ^ n
_∨-𝔏_ {zero} a b = ↥ tt
_∨-𝔏_ {suc zero} a b = a ⊔ b
_∨-𝔏_ {suc (suc n)} (a , as) (b , bs) = (a ⊔ b) , _∨-𝔏_ as bs

{-
module _ where
  private
    f : 𝔏 ^ n -> 𝔏 ^ n -> 𝔏 ^ n
    f {zero} a b = ↥ tt
    f {suc zero} a b = a ⊔ b
    f {suc (suc n)} (a , as) (b , bs) = (a ⊔ b) , f as bs


    unit-l-⋅-𝔏 : ∀{v : 𝔏 ^ n} -> f (many ℓ₀) v ≡ v
    unit-l-⋅-𝔏 {n = zero} {↥ tt} = refl
    unit-l-⋅-𝔏 {n = suc zero} = refl
    unit-l-⋅-𝔏 {n = suc (suc n)} {v , vs} = λ i -> v , unit-l-⋅-𝔏 {v = vs} i

    unit-r-⋅-𝔏 : ∀{v : 𝔏 ^ n} -> f v (many ℓ₀) ≡ v
    unit-r-⋅-𝔏 {n = zero} {↥ tt} = refl
    unit-r-⋅-𝔏 {n = suc zero} = refl
    unit-r-⋅-𝔏 {n = suc (suc n)} {v , vs} = λ i -> v , unit-r-⋅-𝔏 {v = vs} i

    assoc-⋅-𝔏 : ∀{u v w : 𝔏 ^ n} -> f (f u v) w ≡ f u (f v w)
    assoc-⋅-𝔏 {n = n} {u} {v} {w} = {!!}

  Monoid:𝔏 : ∀{n : ℕ} -> Monoid ℓ₀
  ⟨ Monoid:𝔏 {n} ⟩ = 𝔏 ^ n
  IMonoid.𝟷 (of Monoid:𝔏 {n}) = many ℓ₀
  IMonoid._⋅_ (of Monoid:𝔏 {n}) = f
  IMonoid.assoc-⋅ (of Monoid:𝔏 {n}) = assoc-⋅-𝔏
  IMonoid.unit-l-⋅ (of Monoid:𝔏 {n}) = unit-l-⋅-𝔏
  IMonoid.unit-r-⋅ (of Monoid:𝔏 {n}) = unit-r-⋅-𝔏

  instance IMonoid:𝔏 = #openstruct Monoid:𝔏
  -}





Category:Lift : Category 𝑖 -> Category (𝑖 ∨ 𝑗)
⟨ Category:Lift {𝑖 = 𝑖} {𝑗 = 𝑗} 𝒞 ⟩ = Lift {j = 𝑗 ⌄ 0} ⟨ 𝒞 ⟩
isCategory.Hom (of Category:Lift {𝑗 = 𝑗} 𝒞) (↥ a) (↥ b) = Lift {j = 𝑗 ⌄ 1} (Hom a b)
isCategory._≣_ (of Category:Lift {𝑗 = 𝑗} 𝒞) (↥ f) (↥ g) = Lift {j = 𝑗 ⌄ 2} (f ≣ g)
isEquivRel.refl (isCategory.isEquivRel:≣ (of Category:Lift 𝒞)) = ↥ refl
isEquivRel.sym (isCategory.isEquivRel:≣ (of Category:Lift 𝒞)) (↥ p) = ↥ (sym p)
isEquivRel._∙_ (isCategory.isEquivRel:≣ (of Category:Lift 𝒞)) (↥ p) (↥ q) = ↥ (p ∙ q)
isCategory.id (of Category:Lift 𝒞) = ↥ id
isCategory._◆_ (of Category:Lift 𝒞) (↥ f) (↥ g) = ↥ (f ◆ g)
isCategory.unit-l-◆ (of Category:Lift 𝒞) = {!!}
isCategory.unit-r-◆ (of Category:Lift 𝒞) = {!!}
isCategory.unit-2-◆ (of Category:Lift 𝒞) = {!!}
isCategory.assoc-l-◆ (of Category:Lift 𝒞) = {!!}
isCategory.assoc-r-◆ (of Category:Lift 𝒞) = {!!}
isCategory._◈_ (of Category:Lift 𝒞) = {!!}


-- instance
--   isCategory:Lift : ∀{X : 𝒰 𝑖} {{_ : isCategory X 𝑗}} -> isCategory (Lift {j = 𝑘} X) (𝑗 ⋅ 𝑙)
--   isCategory:Lift = {!!}


record Notation-Lift (P : (𝑖 : 𝔏 ^ n) -> 𝒰 (𝑖 ⁺)) : 𝒰ω where
  field ↑_ : ∀{𝑖 𝑗} -> P 𝑖 -> P (𝑖 ∨-𝔏 𝑗)
  infixr 200 ↑_
open Notation-Lift {{...}} public

instance
  Notation-Lift:Category : Notation-Lift Category
  Notation-Lift.↑_ Notation-Lift:Category {v} {w} = Category:Lift {𝑖 = v} {𝑗 = w}

-- ↑₀ : Category (many ℓ₀) -> Category 𝑗
-- ↑₀ 𝒞 = ↑ 𝒞
