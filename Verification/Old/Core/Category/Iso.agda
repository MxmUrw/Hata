
{-# OPTIONS --cubical --allow-unsolved-metas #-}

module Verification.Old.Core.Category.Iso where

open import Verification.Conventions
open import Verification.Old.Core.Category.Definition
-- open import Verification.Old.Core.Category.Instance.Cat
open import Verification.Old.Core.Category.Instance.Type.Definition

module _ {X : 𝒰 𝑖} {{_ : isCategory X 𝑗}} where

  record IIso (a b : X) (f : a ⟶ b) : 𝒰 (𝑗 ⌄ 0 ⊔ 𝑗 ⌄ 1) where
    field inverse : b ⟶ a
          /⟲ : f ◆ inverse ≣ id
          /⟳ : inverse ◆ f ≣ id

unquoteDecl _≅_ iso = #struct "Iso" (quote IIso) "f" _≅_ iso
open IIso public

module _ {X : Category 𝑖} {a b : ⟨ X ⟩} where
  -- instance
    Notation-Inverse:Iso : Notation-Inverse (a ≅ b) (b ≅ a)
    ⟨ (Notation-Inverse:Iso Notation-Inverse.⁻¹) x ⟩ = inverse (of x)
    IIso.inverse (of ((Notation-Inverse:Iso Notation-Inverse.⁻¹) x)) = ⟨ x ⟩
    IIso./⟲ (of ((Notation-Inverse:Iso Notation-Inverse.⁻¹) x)) = /⟳ (of x)
    IIso./⟳ (of ((Notation-Inverse:Iso Notation-Inverse.⁻¹) x)) = /⟲ (of x)

infixl 50 _◆-𝒰_
_◆-𝒰_ = comp-𝒰

record IIso-𝒰 (a : 𝒰 𝑖) (b : 𝒰 𝑗) (f : a -> b) : 𝒰 (𝑖 ､ 𝑗) where
  field inverse-𝒰 : b -> a
        /⟲-𝒰 : f ◆-𝒰 inverse-𝒰 ≡ id
        /⟳-𝒰 : inverse-𝒰 ◆-𝒰 f ≡ id
open IIso-𝒰 {{...}} public
unquoteDecl _≅-𝒰_ iso-𝒰 = #struct "TyIso" (quote IIso-𝒰) "f" _≅-𝒰_ iso-𝒰

module _ {a : 𝒰 𝑖} {b : 𝒰 𝑗} where
  instance
    Notation-Inverse:Iso-𝒰 : Notation-Inverse (a ≅-𝒰 b) (b ≅-𝒰 a)
    ⟨ (Notation-Inverse:Iso-𝒰 Notation-Inverse.⁻¹) x ⟩ = inverse-𝒰
    IIso-𝒰.inverse-𝒰 (of ((Notation-Inverse:Iso-𝒰 Notation-Inverse.⁻¹) x)) = ⟨ x ⟩
    IIso-𝒰./⟲-𝒰 (of ((Notation-Inverse:Iso-𝒰 Notation-Inverse.⁻¹) x)) = /⟳-𝒰
    IIso-𝒰./⟳-𝒰 (of ((Notation-Inverse:Iso-𝒰 Notation-Inverse.⁻¹) x)) = /⟲-𝒰


-- record Abstract (A : 𝒰 𝑖) (B : 𝒰 𝑗) : 𝒰 (𝑖 ､ 𝑗) where
--   field abstraction : A ≅-𝒰 B
--   abst : A -> B
--   abst = ⟨ abstraction ⟩
--   conc : B -> A
--   conc = ⟨ abstraction ⁻¹ ⟩
-- open Abstract {{...}} public


record ILiftHom {X : 𝒰 𝑖} {{_ : isCategory X 𝑗}} (a b : X) (A : 𝒰 𝑘) : 𝒰 (𝑗 ､ 𝑖 ､ 𝑘) where
  field liftHom : A ≅-𝒰 (Hom a b)
open ILiftHom {{...}} public


