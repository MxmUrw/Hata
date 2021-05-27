

{-# OPTIONS --cubical --allow-unsolved-metas #-}

module Verification.Core.Algebra.Basic.Ring where

open import Verification.Conventions
open import Verification.Core.Category.Definition
open import Verification.Core.Algebra.Basic.Monoid
open import Verification.Core.Algebra.Basic.Abelian


-- ===* Rings
-- | We define rings as sets with compatible abelian and monoid structures.

-- [Hide]

record IRing (R : 𝒰 𝑖) : 𝒰 𝑖 where
  field {{Multiplicative}} : IMonoid R
        {{Additive}} : IAbelian R
unquoteDecl Ring ring = #struct "Ring" (quote IRing) "R" Ring ring

record IRingHom (R : Ring 𝑖) (S : Ring 𝑗) (f : ⟨ R ⟩ -> ⟨ S ⟩) : 𝒰 (𝑖 ⊔ 𝑗) where

unquoteDecl RingHom ringhom = #struct "RingHom" (quote IRingHom) "f" RingHom ringhom

instance
  isCategory:Ring : isCategory (Ring 𝑖) (𝑖 , 𝑖)
  isCategory.Hom isCategory:Ring = RingHom
  isCategory._≣_ isCategory:Ring = {!!}
  isCategory.isEquivRel:≣ isCategory:Ring = {!!}
  isCategory.id isCategory:Ring = {!!}
  isCategory._◆_ isCategory:Ring = {!!}
  isCategory._◈_ isCategory:Ring = {!!}
  isCategory.unit-l-◆ isCategory:Ring = {!!}
  isCategory.unit-r-◆ isCategory:Ring = {!!}
  isCategory.unit-2-◆ isCategory:Ring = {!!}
  isCategory.assoc-l-◆ isCategory:Ring = {!!}
  isCategory.assoc-r-◆ isCategory:Ring = {!!}


instance
  IAbelianHom:scale : {R : 𝒰 𝑖} {{_ : IRing R}} -> ∀{r : R} -> IAbelianHom (′ R ′) (′ R ′) (r ⋅_)
  unwrap IAbelianHom:scale = record {}

AbelianHom:scale : {R : Ring 𝑖} -> ∀(r : ⟨ R ⟩) -> AbelianHom (′ ⟨ R ⟩ ′) (′ ⟨ R ⟩ ′)
⟨ AbelianHom:scale r ⟩ = r ⋅_
(of (AbelianHom:scale r)) = IAbelianHom:scale


-- //

