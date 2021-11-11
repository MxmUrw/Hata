
{-# OPTIONS --cubical --allow-unsolved-metas #-}

module Verification.Old.Core.Algebra.Basic.Group where

open import Verification.Conventions
open import Verification.Old.Core.Category.Definition
open import Verification.Old.Core.Category.Instance.Type
open import Verification.Old.Core.Algebra.Basic.Monoid


-- === Groups
-- | We define groups as monoids with an inverse involution.

-- [Hide]

record IMonoid:WithInverse (A : 𝒰 𝑖) {{_ : IMonoid A}} : 𝒰 𝑖 where
  field _⁻¹-Monoid : A -> A
open IMonoid:WithInverse {{...}} public

record IGroup (A : 𝒰 𝑖) : 𝒰 𝑖 where
  field {{Impl1}} : IMonoid A
        {{Impl2}} : IMonoid:WithInverse A
open IGroup {{...}} public
unquoteDecl Group group = #struct "Grp" (quote IGroup) "A" Group group

IGroupHom : (M : Group 𝑖) (N : Group 𝑗) (f : ⟨ M ⟩ -> ⟨ N ⟩) -> 𝒰 (𝑖 ⊔ 𝑗)
IGroupHom M N f = IMonoidHom (monoid ⟨ M ⟩ {{Impl1 {A = ⟨ M ⟩}}}) (monoid ⟨ N ⟩) f

unquoteDecl GroupHom groupHom = #struct "GrpHom" (quote IGroupHom) "f" GroupHom groupHom

instance
  INotation:Inverse:Group : {A : 𝒰 𝑖} {{_ : IGroup A}} -> Notation-Inverse A A
  INotation:Inverse:Group Notation-Inverse.⁻¹ = _⁻¹-Monoid

instance
  IMonoidHom:⁻¹ : ∀{A : 𝒰 𝑖} {{_ : IGroup A}} -> IMonoidHom (′ A ′) (′ A ′) _⁻¹-Monoid
  IMonoidHom:⁻¹ = record {}

-- //


