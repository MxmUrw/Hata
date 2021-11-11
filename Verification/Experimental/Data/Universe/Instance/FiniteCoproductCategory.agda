
module Verification.Core.Data.Universe.Instance.FiniteCoproductCategory where

open import Verification.Conventions

open import Verification.Core.Set.Setoid.Definition
open import Verification.Core.Data.Universe.Definition
open import Verification.Core.Data.Sum.Definition
open import Verification.Core.Category.Std.Morphism.Iso
open import Verification.Core.Category.Std.Category.Definition
-- open import Verification.Core.Category.Std.Category.Construction.Product
open import Verification.Core.Category.Std.Functor.Definition
-- open import Verification.Core.Category.Std.Category.Structured.Monoidal.Definition
-- open import Verification.Core.Algebra.Monoid.Definition
open import Verification.Core.Data.Universe.Instance.Category
open import Verification.Core.Category.Std.Natural.Iso
open import Verification.Core.Category.Std.Limit.Specific.Coproduct.Definition
open import Verification.Core.Category.Std.Limit.Specific.Product
open import Verification.Core.Category.Std.Category.Structured.FiniteCoproduct.Definition
open import Verification.Core.Category.Std.Category.Structured.FiniteProduct.Definition
open import Verification.Core.Category.Std.Category.Structured.FiniteProduct.As.Monoid
open import Verification.Core.Category.Std.Category.Structured.FiniteCoproduct.As.FiniteProduct


module _ {a b : 𝒰 𝑖} where
  instance
    isCoproduct:+-𝒰 : isCoproduct a b (a + b)
    isCoproduct.ι₀ isCoproduct:+-𝒰 = left
    isCoproduct.ι₁ isCoproduct:+-𝒰 = right
    isCoproduct.⦗ isCoproduct:+-𝒰 ⦘ = λ (f , g) -> either f g
    isCoproduct.isSetoidHom:⦗⦘ isCoproduct:+-𝒰 = record { cong-∼ = λ (p , q) i x → either (p i) (q i) x }
    isCoproduct.reduce-ι₀ isCoproduct:+-𝒰 = refl
    isCoproduct.reduce-ι₁ isCoproduct:+-𝒰 = refl
    isCoproduct.expand-ι₀,ι₁ isCoproduct:+-𝒰 {f = f} = λ { i (left x) -> f (left x)
                                                   ; i (right x) -> f (right x)}

instance
  isInitial:⊥-𝒰 : isInitial (⊥-𝒰 {𝑖})
  isInitial.elim-⊥ isInitial:⊥-𝒰 = λ ()
  isInitial.expand-⊥ isInitial:⊥-𝒰 = λ {i ()}

instance
  hasCoproducts:𝐔𝐧𝐢𝐯 : hasCoproducts (𝐔𝐧𝐢𝐯 𝑖)
  hasCoproducts._⊔_ hasCoproducts:𝐔𝐧𝐢𝐯            = _+-𝒰_
  hasCoproducts.isCoproduct:⊔ hasCoproducts:𝐔𝐧𝐢𝐯  = it

instance
  hasInitial:𝐔𝐧𝐢𝐯 : hasInitial (𝐔𝐧𝐢𝐯 𝑖)
  hasInitial.⊥ hasInitial:𝐔𝐧𝐢𝐯            = ⊥-𝒰
  hasInitial.isInitial:⊥ hasInitial:𝐔𝐧𝐢𝐯  = it

instance
  hasFiniteCoproducts:𝐔𝐧𝐢𝐯 : hasFiniteCoproducts (𝐔𝐧𝐢𝐯 𝑖)
  hasFiniteCoproducts:𝐔𝐧𝐢𝐯 = hasFiniteCoproducts:default

  -- hasFiniteCoproducts._⊔_ hasFiniteCoproducts:𝐔𝐧𝐢𝐯            = _+-𝒰_
  -- hasFiniteCoproducts.isCoproduct:⊔ hasFiniteCoproducts:𝐔𝐧𝐢𝐯  = it
  -- hasFiniteCoproducts.⊥ hasFiniteCoproducts:𝐔𝐧𝐢𝐯              = ⊥-𝒰
  -- hasFiniteCoproducts.isInitial:⊥ hasFiniteCoproducts:𝐔𝐧𝐢𝐯    = it




