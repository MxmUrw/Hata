
module Verification.Experimental.Category.Std.Monad.Instance.LargeCategory where

open import Verification.Conventions

open import Verification.Experimental.Set.Setoid
open import Verification.Experimental.Category.Std.Category.Definition
open import Verification.Experimental.Category.Std.Category.Opposite
open import Verification.Experimental.Category.Std.Functor.Definition
open import Verification.Experimental.Category.Std.Functor.Instance.Category
open import Verification.Experimental.Category.Std.Natural.Definition
open import Verification.Experimental.Category.Std.Natural.Instance.Setoid
open import Verification.Experimental.Category.Std.Category.Instance.Category
open import Verification.Experimental.Category.Std.Monad.Definition
open import Verification.Experimental.Category.Std.Morphism.Iso

--
-- definition from https://ncatlab.org/nlab/show/monad
--
-- (but with oplax morphisms between monads)
--

record 大Monad (𝑖 : 𝔏 ^ 3) : 𝒰 (𝑖 ⁺) where
  constructor _,_
  field fst : Category 𝑖
  field snd : Monad fst

open 大Monad public

module _ (𝑖 : 𝔏 ^ 3) where
  macro 大𝐌𝐧𝐝 = #structureOn (大Monad 𝑖)

record 大MonadHom (a : 大Monad 𝑖) (b : 大Monad 𝑗) : 𝒰 (𝑖 ､ 𝑗) where
  field fst : Functor (fst a) (fst b)
  field snd : Natural (′ ⟨ snd a ⟩ ′ ◆-𝐂𝐚𝐭 fst) (fst ◆-𝐂𝐚𝐭 ′ ⟨ snd b ⟩ ′)
  -- satisfying ...

open 大MonadHom public


module _ {a : 大Monad 𝑖} {b : 大Monad 𝑗} where

  record 大MonadTrans (f g : 大MonadHom a b) : 𝒰 (𝑖 ､ 𝑗) where
    constructor incl
    field ⟨_⟩ : fst f ⟶ fst g
    -- satisfying ...

  open 大MonadTrans public

  module _ {f g : 大MonadHom a b} where
    instance
      isSetoid:大MonadTrans : isSetoid (大MonadTrans f g)
      isSetoid:大MonadTrans = setoid (λ α β → ⟨ α ⟩ ∼ ⟨ β ⟩) {!!} {!!} {!!}


  instance
    isCategory:大MonadHom : isCategory (大MonadHom a b)
    isCategory.Hom isCategory:大MonadHom = 大MonadTrans
    isCategory.isSetoid:Hom isCategory:大MonadHom = isSetoid:大MonadTrans
    isCategory.id isCategory:大MonadHom = {!!}
    isCategory._◆_ isCategory:大MonadHom = {!!}
    isCategory.unit-l-◆ isCategory:大MonadHom = {!!}
    isCategory.unit-r-◆ isCategory:大MonadHom = {!!}
    isCategory.unit-2-◆ isCategory:大MonadHom = {!!}
    isCategory.assoc-l-◆ isCategory:大MonadHom = {!!}
    isCategory.assoc-r-◆ isCategory:大MonadHom = {!!}
    isCategory._◈_ isCategory:大MonadHom = {!!}

    isSetoid:大MonadHom : isSetoid (大MonadHom a b)
    isSetoid:大MonadHom = isSetoid:byCategory


instance
  isCategory:大𝐌𝐧𝐝 : isCategory (大𝐌𝐧𝐝 𝑖)
  isCategory.Hom isCategory:大𝐌𝐧𝐝 = 大MonadHom
  isCategory.isSetoid:Hom isCategory:大𝐌𝐧𝐝 = isSetoid:大MonadHom
  isCategory.id isCategory:大𝐌𝐧𝐝 = {!!}
  isCategory._◆_ isCategory:大𝐌𝐧𝐝 = {!!}
  isCategory.unit-l-◆ isCategory:大𝐌𝐧𝐝 = {!!}
  isCategory.unit-r-◆ isCategory:大𝐌𝐧𝐝 = {!!}
  isCategory.unit-2-◆ isCategory:大𝐌𝐧𝐝 = {!!}
  isCategory.assoc-l-◆ isCategory:大𝐌𝐧𝐝 = {!!}
  isCategory.assoc-r-◆ isCategory:大𝐌𝐧𝐝 = {!!}
  isCategory._◈_ isCategory:大𝐌𝐧𝐝 = {!!}







