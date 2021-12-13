
module Verification.Core.Data.Language.HindleyMilner.Type.Variant.FirstOrderTermTerm.Signature where


open import Verification.Conventions hiding (ℕ ; _⊔_)
open import Verification.Core.Set.Setoid.Definition
open import Verification.Core.Set.Discrete
open import Verification.Core.Algebra.Monoid.Definition

open import Verification.Core.Data.Product.Definition

open import Verification.Core.Data.List.Variant.Binary.Natural
open import Verification.Core.Data.Universe.Instance.Category
open import Verification.Core.Data.List.Variant.Unary.Definition
open import Verification.Core.Data.List.Variant.Unary.Element
open import Verification.Core.Data.List.Variant.Unary.Natural
open import Verification.Core.Data.List.Variant.Binary.Definition
open import Verification.Core.Data.List.Dependent.Variant.Unary.Definition
open import Verification.Core.Data.List.Dependent.Variant.Binary.Definition
open import Verification.Core.Data.Substitution.Variant.Base.Definition

open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Category.Std.Limit.Specific.Coequalizer
open import Verification.Core.Category.Std.Limit.Specific.Coproduct.Definition
open import Verification.Core.Category.Std.Limit.Specific.Coproduct.Instance.Functor
open import Verification.Core.Computation.Unification.Definition

open import Verification.Core.Theory.Std.Specific.FirstOrderTerm.Param
open import Verification.Core.Theory.Std.Specific.FirstOrderTerm.Definition
open import Verification.Core.Theory.Std.Specific.FirstOrderTerm.Instance.Functor
open import Verification.Core.Theory.Std.Specific.FirstOrderTerm.Instance.RelativeMonad
open import Verification.Core.Theory.Std.Specific.FirstOrderTerm.Unification

open import Verification.Core.Data.Language.HindleyMilner.Helpers



-------------------------------------------------
-- Definition of the data for the HM types

-- [Definition]
-- | The signature for monotypes with a "boolean" and
--   "natural numbers" type constant is given as follows:

-- | 1. There is only one sort, so we define the type
--      of sorts as:
𝒹₀ : 𝒰₀
𝒹₀ = ⊤-𝒰

pattern tyᵗ = tt

-- | 2. The constructors include the boolean, nat types,
--      as well as the obligatory arrow type.
data 𝒹₁ : List 𝒹₀ → 𝒹₀ → 𝒰 ℓ₀ where
  ⇒ᵗ : 𝒹₁ (tyᵗ ∷ tyᵗ ∷ []) tyᵗ
  ℕᵗ : 𝒹₁ [] tyᵗ
  𝔹ᵗ : 𝒹₁ [] tyᵗ

-- | 3. We show that the constructor type is discrete.
instance
  isDiscrete:𝒹₁ : ∀{xs : List 𝒹₀} {x : 𝒹₀} -> isDiscrete (𝒹₁ xs x)
  isDiscrete:𝒹₁ {xs} {x} = record { _≟-Str_ = lem-1 }
    where
      lem-1 : (a b : 𝒹₁ xs x) → Decision (a ≡-Str b)
      lem-1 ⇒ᵗ ⇒ᵗ = yes refl-≣
      lem-1 ℕᵗ ℕᵗ = yes refl-≣
      lem-1 ℕᵗ 𝔹ᵗ = no (λ ())
      lem-1 𝔹ᵗ ℕᵗ = no (λ ())
      lem-1 𝔹ᵗ 𝔹ᵗ = yes refl-≣

-- |> And that the sort type is a set.
instance
  isSet:𝒹₀ : isSet-Str (𝒹₀)
  isSet:𝒹₀ = {!!}

-- |: This makes |𝒹| into a signature for simple terms.
𝒹 : 𝒯⊔Param ℓ₀
𝒹 = record { Sort = 𝒹₀ ; Con = 𝒹₁ }

-- //


-- [Hide]
infixr 30 _⇒_
pattern _⇒_ a b = con ⇒ᵗ (incl a ⋆-⧜ (incl b ⋆-⧜ ◌-⧜))

-- //

