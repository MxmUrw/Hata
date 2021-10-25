
module Verification.Experimental.Theory.Std.Inference.TextInfer where

open import Verification.Conventions hiding (lookup ; ℕ)



open import Verification.Experimental.Set.Setoid.Definition
open import Verification.Experimental.Set.Setoid.Instance.Category
open import Verification.Experimental.Data.Nat.Free
open import Verification.Experimental.Data.Universe.Everything
open import Verification.Experimental.Category.Std.Category.Definition
open import Verification.Experimental.Category.Std.Category.Opposite
open import Verification.Experimental.Category.Std.Functor.Definition
open import Verification.Experimental.Category.Std.Morphism.Iso

open import Verification.Experimental.Category.Std.Monad.Definition
open import Verification.Experimental.Category.Std.Monad.Instance.LargeCategory
open import Verification.Experimental.Category.Std.RelativeMonad.Finitary.Definition
-- open import Verification.Experimental.Category.Std.Monad.KleisliCategory.Instance.Monoidal
open import Verification.Experimental.Category.Std.Monad.TypeMonadNotation
open import Verification.Experimental.Data.AllOf.Sum
open import Verification.Experimental.Data.Substitution.Definition
open import Verification.Experimental.Data.Indexed.Definition
open import Verification.Experimental.Data.Indexed.Instance.Monoid
open import Verification.Experimental.Data.FiniteIndexed.Definition

open import Verification.Experimental.Algebra.Monoid.Free
open import Verification.Experimental.Algebra.Monoid.Free.Element
open import Verification.Experimental.Category.Std.Category.Subcategory.Full
open import Verification.Experimental.Category.Std.Category.Instance.Category
open import Verification.Experimental.Category.Std.Limit.Specific.Coproduct.Definition

open import Verification.Experimental.Theory.Std.Inference.Definition


record hasTextInfer (t : 𝐈𝐧𝐟𝐞𝐫 𝑖) : 𝒰 (𝑖 ⁺) where
  field RepObj : ⟨ fst ⟨ t ⟩ ⟩
  field TIObj : ⟨ fst ⟨ t ⟩ ⟩
  field RepType : Setoid _
  field rep : (RepObj ⟶ ⟨ snd ⟨ t ⟩ ⟩ TIObj) ≅ RepType

  field parse : Text -> Text + RepType
  field {{IShow:TI}} : IShow ⟨ RepType ⟩

open hasTextInfer public



