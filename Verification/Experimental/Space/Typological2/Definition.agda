
module Verification.Core.Space.Typological2.Definition where

open import Verification.Conventions hiding (Discrete ; ∅ ; Bool ; _and_)
open import Verification.Core.Set.Setoid
open import Verification.Core.Set.Decidable
open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Data.Universe.Everything
open import Verification.Core.Data.Prop.Everything
open import Verification.Core.Order.Preorder
open import Verification.Core.Order.Lattice


record isTypological {𝑖 : 𝔏} (A : 𝒰 𝑖) : 𝒰 (𝑖 ⁺) where
  field Base : 𝒰 𝑖
  field ℬ : Base -> (A -> Prop 𝑖)
  field ∅ : Base
  field isEmpty : ∀ {b} -> (ℬ b ∼ ⊥) ↔ (b ≣ ∅)


open isTypological {{...}} public



Typological : ∀ 𝑖 -> 𝒰 _
Typological 𝑖 = 𝒰 𝑖 :& isTypological

macro
  𝐓𝐲𝐩𝐨 : ∀ 𝑖 -> SomeStructure
  𝐓𝐲𝐩𝐨 𝑖 = #structureOn (Typological 𝑖)


-- module _ {A : 𝒰 𝑖} {B : 𝒰 𝑗} where
--   PreImage : (f : A -> B) -> (B -> 𝒰 𝑘) -> (A -> 𝒰 𝑘)

record isContinuous (A B : 𝐓𝐲𝐩𝐨 𝑖) (f : ⟨ A ⟩ -> ⟨ B ⟩) : 𝒰 𝑖 where
  constructor continuous
  field prebase : Base {{of B}} -> Base {{of A}}
  field prebase-valid : ∀ (b : Base {{of B}}) -> (ℬ b ∣ f) ∼ ℬ (prebase b)

open isContinuous {{...}} public

Continuous : (A B : 𝐓𝐲𝐩𝐨 𝑖) -> 𝒰 _
Continuous A B = _ :& isContinuous A B

module _ {A B : 𝐓𝐲𝐩𝐨 𝑖} where
  instance
    isSetoid:Continuous : isSetoid (Continuous A B)
    isSetoid._∼_ isSetoid:Continuous = λ f g -> ⟨ f ⟩ ≡ ⟨ g ⟩
    isSetoid.refl isSetoid:Continuous = refl-≡
    isSetoid.sym isSetoid:Continuous = sym-Path
    isSetoid._∙_ isSetoid:Continuous = trans-Path

id-𝐓𝐲𝐩𝐨 : ∀{A : 𝐓𝐲𝐩𝐨 𝑖} -> Continuous A A
id-𝐓𝐲𝐩𝐨 = id since continuous id λ b → refl

_◆-𝐓𝐲𝐩𝐨_ : ∀{A B C : 𝐓𝐲𝐩𝐨 𝑖} -> (f : Continuous A B) -> (g : Continuous B C) -> Continuous A C
_◆-𝐓𝐲𝐩𝐨_ f g = h since P
  where
    h = ⟨ f ⟩ ◆ ⟨ g ⟩

    P : isContinuous _ _ h
    P = continuous (prebase ◆ prebase) λ b {i} -> (prebase-valid b ∙ prebase-valid (prebase b))


instance
  isCategory:𝐓𝐲𝐩𝐨 : isCategory (𝐓𝐲𝐩𝐨 𝑖)
  isCategory.Hom isCategory:𝐓𝐲𝐩𝐨          = Continuous
  isCategory.isSetoid:Hom isCategory:𝐓𝐲𝐩𝐨 = isSetoid:Continuous
  isCategory.id isCategory:𝐓𝐲𝐩𝐨           = id-𝐓𝐲𝐩𝐨
  isCategory._◆_ isCategory:𝐓𝐲𝐩𝐨          = _◆-𝐓𝐲𝐩𝐨_
  isCategory.unit-l-◆ isCategory:𝐓𝐲𝐩𝐨     = refl-≡
  isCategory.unit-r-◆ isCategory:𝐓𝐲𝐩𝐨     = refl-≡
  isCategory.unit-2-◆ isCategory:𝐓𝐲𝐩𝐨     = refl-≡
  isCategory.assoc-l-◆ isCategory:𝐓𝐲𝐩𝐨    = refl-≡
  isCategory.assoc-r-◆ isCategory:𝐓𝐲𝐩𝐨    = refl-≡
  isCategory._◈_ isCategory:𝐓𝐲𝐩𝐨          = {!!}


