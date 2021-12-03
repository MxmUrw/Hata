
module Verification.Core.Theory.Std.Inference.TextInfer where

open import Verification.Conventions hiding (lookup ; ℕ)



open import Verification.Core.Set.Setoid.Definition
open import Verification.Core.Set.Setoid.Instance.Category
open import Verification.Core.Data.Nat.Free
open import Verification.Core.Data.Universe.Everything
open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Category.Std.Category.Opposite
open import Verification.Core.Category.Std.Functor.Definition
open import Verification.Core.Category.Std.Morphism.Iso

open import Verification.Core.Category.Std.Monad.Definition
open import Verification.Core.Category.Std.Monad.Instance.LargeCategory
open import Verification.Core.Category.Std.RelativeMonad.Finitary.Definition
-- open import Verification.Core.Category.Std.Monad.KleisliCategory.Instance.Monoidal
open import Verification.Core.Category.Std.Monad.TypeMonadNotation
open import Verification.Core.Data.AllOf.Sum
open import Verification.Core.Data.Substitution.Variant.Base.Definition
open import Verification.Core.Data.Indexed.Definition
open import Verification.Core.Data.Indexed.Instance.Monoid
open import Verification.Core.Data.FiniteIndexed.Definition

open import Verification.Core.Algebra.Monoid.Free
open import Verification.Core.Data.List.Variant.FreeMonoid.Element
open import Verification.Core.Category.Std.Category.Subcategory.Full
open import Verification.Core.Category.Std.Category.Instance.Category
open import Verification.Core.Category.Std.Limit.Specific.Coproduct.Definition

open import Verification.Core.Theory.Std.Inference.Definition


record hasTextInfer (t : 𝐈𝐧𝐟𝐞𝐫 𝑖) : 𝒰 (𝑖 ⁺) where
  field RepObj : ⟨ fst ⟨ t ⟩ ⟩
  field TIObj : ⟨ fst ⟨ t ⟩ ⟩
  field RepType : Setoid _
  field rep : (RepObj ⟶ ⟨ snd ⟨ t ⟩ ⟩ TIObj) ≅ RepType

  field parse : Text -> Text + RepType
  field {{IShow:TI}} : IShow ⟨ RepType ⟩

open hasTextInfer public



