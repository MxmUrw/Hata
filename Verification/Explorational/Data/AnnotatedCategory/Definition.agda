
module Verification.Explorational.Data.AnnotatedCategory.Definition where

open import Verification.Conventions hiding (lookup ; ℕ)

open import Verification.Core.Data.Nat.Definition
open import Verification.Core.Set.Setoid.Definition
open import Verification.Core.Set.Setoid.Instance.Category
open import Verification.Core.Data.AllOf.Product
open import Verification.Core.Data.AllOf.Sum
open import Verification.Core.Data.Expr.Variant.Base.Definition
open import Verification.Core.Data.Universe.Everything
open import Verification.Core.Category.Std.AllOf.Collection.Basics
open import Verification.Core.Category.Std.AllOf.Collection.Limits
open import Verification.Core.Set.Setoid.As.Category
open import Verification.Core.Set.Setoid.Discrete
open import Verification.Core.Set.Setoid.Definition

open import Verification.Core.Category.Std.Monad.Definition
open import Verification.Core.Category.Std.Monad.Instance.Category
open import Verification.Core.Category.Std.Monad.Instance.LargeCategory
open import Verification.Core.Theory.Std.Inference.Definition
open import Verification.Core.Theory.Std.Inference.Task
open import Verification.Core.Theory.Std.Inference.TextInfer


module _ (X : 𝒰 𝑖) where
  Times : Functor (𝐔𝐧𝐢𝐯 𝑖) (𝐔𝐧𝐢𝐯 𝑖)
  Times = (λ A -> X × A) since {!!}


module _ (𝒞 : Category 𝑖) where

  record Annotated (𝑗 : 𝔏) : 𝒰 (𝑖 ､ 𝑗 ⁺) where
    field ⟨_⟩ : Functor (𝐔𝐧𝐢𝐯 𝑗) 𝒞

  open Annotated public

  record AnnotatedHom (F G : Annotated 𝑗) : 𝒰 (𝑖 ､ 𝑗 ⁺) where
    field Base : 𝐔𝐧𝐢𝐯 𝑗
    field Hom : Natural (Times Base ◆-𝐂𝐚𝐭 ⟨ F ⟩) ⟨ G ⟩
    -- field ⟨_⟩ : ∑ λ (X : 𝐔𝐧𝐢𝐯 𝑗) ->
    -- ∏ λ (A : 𝐔𝐧𝐢𝐯 𝑗) -> ⟨ F ⟩ (X × A) ⟶ ⟨ G ⟩ A

  open AnnotatedHom public

  module _ {F G : Annotated 𝑗} where
    record _∼-AnnotatedHom_ (α β : AnnotatedHom F G) : 𝒰 (𝑖 ､ 𝑗 ⁺) where
      field baseiso : Base α ≅ Base β
      -- field homeq : ∀ {A} -> (a : ⟨ F ⟩ (fst ⟨ α ⟩ × A)) -> snd ⟨ α ⟩ A a ∼ 

    instance
      isSetoid:AnnotatedHom : isSetoid (AnnotatedHom F G)
      isSetoid:AnnotatedHom = isSetoid:byDef _∼-AnnotatedHom_ {!!} {!!} {!!}
        where
          lem-1 : {x : AnnotatedHom F G} → x ∼-AnnotatedHom x
          lem-1 = {!!}

  id-AnnotatedHom : ∀{F : Annotated 𝑗} -> AnnotatedHom F F
  id-AnnotatedHom = record { Base = ⊤-𝒰 ; Hom = (λ x → map π₁) since {!!} }

  instance
    isCategory:Annotated : isCategory (Annotated 𝑗)
    isCategory.Hom isCategory:Annotated = AnnotatedHom
    isCategory.isSetoid:Hom isCategory:Annotated = it
    isCategory.id isCategory:Annotated = {!!}
    isCategory._◆_ isCategory:Annotated = {!!}
    isCategory.unit-l-◆ isCategory:Annotated = {!!}
    isCategory.unit-r-◆ isCategory:Annotated = {!!}
    isCategory.unit-2-◆ isCategory:Annotated = {!!}
    isCategory.assoc-l-◆ isCategory:Annotated = {!!}
    isCategory.assoc-r-◆ isCategory:Annotated = {!!}
    isCategory._◈_ isCategory:Annotated = {!!}





