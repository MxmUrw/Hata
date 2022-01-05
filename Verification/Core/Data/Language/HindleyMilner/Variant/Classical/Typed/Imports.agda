
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
open import Verification.Core.Theory.Std.Specific.FirstOrderTerm.Signature public
open import Verification.Core.Theory.Std.Specific.FirstOrderTerm.Definition public
open import Verification.Core.Theory.Std.Specific.FirstOrderTerm.Instance.Functor public
open import Verification.Core.Theory.Std.Specific.FirstOrderTerm.Instance.RelativeMonad public
open import Verification.Core.Theory.Std.Specific.FirstOrderTerm.Instance.Unification public

-------------
-- Types as simple terms
open import Verification.Core.Data.Language.HindleyMilner.Type.Variant.FirstOrderTerm.Signature public
open import Verification.Core.Data.Language.HindleyMilner.Type.Variant.FirstOrderTerm.Definition public

-------------
-- Other data

open import Verification.Core.Data.Product.Definition public
open import Verification.Core.Data.Sum.Definition public
open import Verification.Core.Data.Substitution.Variant.Base.Definition public


-------------
-- Specialized category modules
open Overwrite:isCategory:𝐒𝐮𝐛𝐬𝐭-Sim Σ-Sim public
open Overwrite:isCoproduct:𝐒𝐮𝐛𝐬𝐭-Sim Σ-Sim public
open Overwrite:hasCoproducts:𝐒𝐮𝐛𝐬𝐭-Sim Σ-Sim public
open Overwrite:hasFiniteCoproducts:𝐒𝐮𝐛𝐬𝐭-Sim Σ-Sim public
open Overwrite:hasInitial:𝐒𝐮𝐛𝐬𝐭-Sim Σ-Sim public
open Overwrite:isInitial:𝐒𝐮𝐛𝐬𝐭-Sim Σ-Sim public

-------------
-- Other specialized definitions

_⟶_ = Hom

_≅_ = _≅ᵘ_ {𝒞 = 𝐒𝐮𝐛𝐬𝐭-Sim Σ-Sim} {{isCategory:⧜𝐒𝐮𝐛𝐬𝐭 {T = 𝒯⊔term Σ-Sim}}}
⟨_⟩⁻¹ = ⟨_⟩⁻¹ᵘ {𝒞 = 𝐒𝐮𝐛𝐬𝐭-Sim Σ-Sim} {{isCategory:⧜𝐒𝐮𝐛𝐬𝐭 {T = 𝒯⊔term Σ-Sim}}}

-- {-# DISPLAY isCoequalizer.π₌ _ = π₌ #-}
-- {-# DISPLAY isCoproduct.ι₀ _ = ι₀ #-}
-- {-# DISPLAY isCoproduct.ι₁ _ = ι₁ #-}
{-# DISPLAY _内◆-⧜𝐒𝐮𝐛𝐬𝐭_ f g = f ◆ g #-}
{-# DISPLAY 内id-⧜𝐒𝐮𝐛𝐬𝐭 = id #-}







