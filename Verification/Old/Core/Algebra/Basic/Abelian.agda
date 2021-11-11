
{-# OPTIONS --cubical --allow-unsolved-metas #-}

module Verification.Old.Core.Algebra.Basic.Abelian where

open import Verification.Conventions
open import Verification.Old.Core.Category.Definition
open import Verification.Old.Core.Category.Instance.Set.Definition
open import Verification.Old.Core.Algebra.Basic.Group
open import Verification.Old.Core.Algebra.Basic.Monoid


-- ===* Abelian Groups
-- | We define abelian groups by taking the same definition as for groups, but using additive instead of multiplicative notation.

-- [Hide]

-- record Hide (A : 𝒰 𝑖) : 𝒰 𝑖 where
--   constructor hide
--   field unhide : A
-- open Hide public

-- map-Hide : ∀{A : 𝒰 𝑖} {B : 𝒰 𝑗} -> (A -> B) -> (Hide A -> Hide B)
-- map-Hide f (hide x) = hide (f x)

-- instance
--   IFunctor:Hide : IFunctor (⌘ 𝒰 𝑖) (⌘ 𝒰 𝑖) Hide
--   IFunctor.map IFunctor:Hide = map-Hide
--   IFunctor.functoriality-id IFunctor:Hide = {!!}
--   IFunctor.functoriality-◆ IFunctor:Hide = {!!}



record IAbelian (A : 𝒰 𝑖) : 𝒰 𝑖 where
  field AsMult : IMonoid A
        AsMultInv : IMonoid:WithInverse A {{AsMult}}
open IAbelian {{...}} public

module _ {A : 𝒰 𝑖} {{#A : IAbelian A}} where
  infixl 30 _+_
  _+_ : A -> A -> A
  _+_ a b = _⋅_ {{AsMult}} a b

  -_ : A -> A
  -_ a = _⁻¹-Monoid {{AsMult}} {{AsMultInv}} a

  𝟶 : A
  𝟶 = 𝟷 {{AsMult}}

unquoteDecl Abelian abelian = #struct "Ab" (quote IAbelian) "A" Abelian abelian


instance
  INotation:Reinterpret:Abelian : INotation:Reinterpret (Abelian 𝑖) (Group 𝑖)
  ⟨ INotation:Reinterpret.reinterpret INotation:Reinterpret:Abelian A ⟩ = ⟨ A ⟩
  IGroup.Impl1 (of (INotation:Reinterpret.reinterpret INotation:Reinterpret:Abelian A)) = AsMult
  IGroup.Impl2 (of (INotation:Reinterpret.reinterpret INotation:Reinterpret:Abelian A)) = AsMultInv

-- IAbelianHom : (M : Abelian 𝑖) (N : Abelian 𝑗) (f : ⟨ M ⟩ -> ⟨ N ⟩) -> 𝒰 (𝑖 ⊔ 𝑗)
-- IAbelianHom M N f = IGroupHom (reinterpret M) (reinterpret N) f

record IAbelianHom (M : Abelian 𝑖) (N : Abelian 𝑗) (f : ⟨ M ⟩ -> ⟨ N ⟩) : 𝒰 (𝑖 ⊔ 𝑗) where
  field unwrap : IGroupHom (reinterpret M) (reinterpret N) f
open IAbelianHom public

unquoteDecl AbelianHom abelianHom = #struct "AbHom" (quote IAbelianHom) "f" AbelianHom abelianHom

instance
  INotation:Reinterpret:AbelianHom : ∀{M : Abelian 𝑖} {N : Abelian 𝑗} -> INotation:Reinterpret (AbelianHom M N) (GroupHom (reinterpret M) (reinterpret N))
  INotation:Reinterpret.reinterpret (INotation:Reinterpret:AbelianHom {M = M} {N = N}) f = groupHom {M = (reinterpret M)} {N = (reinterpret N)} ⟨ f ⟩ {{(of f) .unwrap}}

-- AbelianHom : (M : Abelian 𝑖) (N : Abelian 𝑗) -> 𝒰 (𝑖 ⊔ 𝑗)
-- AbelianHom M N = MonoidHom ((⌘ ⟨ M ⟩) {{AsMult}}) ((⌘ ⟨ N ⟩) {{AsMult}})

  -- ⟨ INotation:Reinterpret.reinterpret INotation:Reinterpret:Abelian A ⟩ = ⟨ A ⟩
  -- IMonoid.𝟷 (of (of (INotation:Reinterpret.reinterpret INotation:Reinterpret:Abelian A))) = 𝟶
  -- IMonoid._⋅_ (of (of (INotation:Reinterpret.reinterpret INotation:Reinterpret:Abelian A))) = _+_
  -- of (INotation:Reinterpret.reinterpret INotation:Reinterpret:Abelian A) ⁻¹-Group = -_

{-

record IAbelian (A : 𝒰 𝑖) : 𝒰 𝑖 where
  field instance asGroup : IGroup (Hide A)
  𝟶 : A
  𝟶 = unhide 𝟷
  -_ : A -> A
  - x = unhide ((hide x) ⁻¹)
  _+_ : A -> A -> A
  a + b = unhide (hide a ⋅ hide b)

open IAbelian {{...}} public

IAbelianHom : (M : Abelian 𝑖) (N : Abelian 𝑗) (f : ⟨ M ⟩ -> ⟨ N ⟩) -> 𝒰 (𝑖 ⊔ 𝑗)
IAbelianHom M N f = IMonoidHom (⌘ Hide (⟨ M ⟩)) (⌘ Hide ⟨ N ⟩) (map-Hide f)

AbelianHom : (M : Abelian 𝑖) (N : Abelian 𝑗) -> 𝒰 (𝑖 ⊔ 𝑗)
AbelianHom M N = MonoidHom (⌘ Hide (⟨ M ⟩)) (⌘ Hide ⟨ N ⟩)

abelianHom : {M : Abelian 𝑖} {N : Abelian 𝑗} (f : ⟨ M ⟩ -> ⟨ N ⟩) {{_ : IAbelianHom M N f}} -> AbelianHom M N
abelianHom f = monoidHom (map-Hide f)

-- record IAbelianHom (M : Abelian 𝑖) (N : Abelian 𝑗) (f : ⟨ M ⟩ -> ⟨ N ⟩) : 𝒰 (𝑖 ⊔ 𝑗) where
-- unquoteDecl AbelianHom abelianHom = #struct (quote IAbelianHom) "f" AbelianHom abelianHom



open IGroup


-}

-- //
