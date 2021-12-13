
module Verification.Core.Data.Language.HindleyMilner.Variant.Classical.Typed.Imports where

-------------
-- Classes
open import Verification.Core.Set.Setoid.Definition public
open import Verification.Core.Order.Preorder public
open import Verification.Core.Set.Discrete public
open import Verification.Core.Algebra.Monoid.Definition public

-------------
-- Categories and unification
open import Verification.Core.Category.Std.Morphism.Iso public renaming (_≅_ to _≅ᵘ_ ; ⟨_⟩⁻¹ to ⟨_⟩⁻¹ᵘ)
open import Verification.Core.Category.Std.Morphism.Epi.Definition public
open import Verification.Core.Category.Std.Category.Subcategory.Full public
open import Verification.Core.Category.Std.Limit.Specific.Coequalizer public
-- open import Verification.Core.Category.Std.Limit.Specific.Coproduct.Definition
open import Verification.Core.Category.Std.Limit.Specific.Coproduct.Definition using (append-⦗⦘ ; ⦗≀_≀⦘) public
open import Verification.Core.Category.Std.Limit.Specific.Coproduct.Instance.Functor public
open import Verification.Core.Category.Std.Factorization.EpiMono.Variant.Split.Definition public
open import Verification.Core.Computation.Unification.Definition public

-------------
-- Lists
open import Verification.Core.Data.List.Variant.Unary.Definition public
open import Verification.Core.Data.List.Variant.Unary.Element public
open import Verification.Core.Data.List.Variant.Unary.Natural public
open import Verification.Core.Data.List.Variant.Binary.Definition public
open import Verification.Core.Data.List.Variant.Binary.Instance.Monoid public
open import Verification.Core.Data.List.Variant.Binary.Natural public
open import Verification.Core.Data.List.Variant.Unary.Element public
open import Verification.Core.Data.List.Variant.Binary.Element.Definition public
open import Verification.Core.Data.List.Dependent.Variant.Unary.Definition public
open import Verification.Core.Data.List.Dependent.Variant.Binary.Definition public

-------------
-- Simple terms
open import Verification.Core.Theory.Std.Specific.FirstOrderTerm.Param public
open import Verification.Core.Theory.Std.Specific.FirstOrderTerm.Definition public
open import Verification.Core.Theory.Std.Specific.FirstOrderTerm.Instance.Functor public
open import Verification.Core.Theory.Std.Specific.FirstOrderTerm.Instance.RelativeMonad public
open import Verification.Core.Theory.Std.Specific.FirstOrderTerm.Unification public

-------------
-- Types as simple terms
open import Verification.Core.Data.Language.HindleyMilner.Type.Variant.FirstOrderTermTerm.Signature public
open import Verification.Core.Data.Language.HindleyMilner.Type.Variant.FirstOrderTermTerm.Definition public

-------------
-- Other data

open import Verification.Core.Data.Product.Definition public
open import Verification.Core.Data.Sum.Definition public
open import Verification.Core.Data.Substitution.Variant.Base.Definition public


-------------
-- Specialized category modules
open Overwrite:isCategory:⧜𝒯⊔Term 𝒹 public
open Overwrite:isCoproduct:⧜𝒯⊔Term 𝒹 public
open Overwrite:hasCoproducts:⧜𝒯⊔Term 𝒹 public
open Overwrite:hasFiniteCoproducts:⧜𝒯⊔Term 𝒹 public
open Overwrite:hasInitial:⧜𝒯⊔Term 𝒹 public
open Overwrite:isInitial:⧜𝒯⊔Term 𝒹 public

-------------
-- Other specialized definitions

_⟶_ = Hom

_≅_ = _≅ᵘ_ {𝒞 = ⧜𝒯⊔Term 𝒹} {{isCategory:⧜𝐒𝐮𝐛𝐬𝐭 {T = 𝒯⊔term 𝒹}}}
⟨_⟩⁻¹ = ⟨_⟩⁻¹ᵘ {𝒞 = ⧜𝒯⊔Term 𝒹} {{isCategory:⧜𝐒𝐮𝐛𝐬𝐭 {T = 𝒯⊔term 𝒹}}}

-- {-# DISPLAY isCoequalizer.π₌ _ = π₌ #-}
-- {-# DISPLAY isCoproduct.ι₀ _ = ι₀ #-}
-- {-# DISPLAY isCoproduct.ι₁ _ = ι₁ #-}
{-# DISPLAY _内◆-⧜𝐒𝐮𝐛𝐬𝐭_ f g = f ◆ g #-}
{-# DISPLAY 内id-⧜𝐒𝐮𝐛𝐬𝐭 = id #-}







