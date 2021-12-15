
module Verification.Core.Data.Language.HindleyMilner.Type.Variant.FirstOrderTerm.Signature where


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

open import Verification.Core.Theory.Std.Specific.FirstOrderTerm.Signature
open import Verification.Core.Theory.Std.Specific.FirstOrderTerm.Definition
open import Verification.Core.Theory.Std.Specific.FirstOrderTerm.Instance.Functor
open import Verification.Core.Theory.Std.Specific.FirstOrderTerm.Instance.RelativeMonad
open import Verification.Core.Theory.Std.Specific.FirstOrderTerm.Unification

open import Verification.Core.Data.Language.HindleyMilner.Helpers



-------------------------------------------------
-- Simple types in terms of first order terms

-- | As a concrete example, we show how the
--   simple types from Definition REF can be
--   expressed as first order terms.
--   For this, a signature |Σ-Sim| needs to be defined.
--   Since the terms of |Ty-Sim| do not have different sorts,
--   the type [..] of sorts is given by [...,]
Sort-Sim : 𝒰₀
Sort-Sim = ⊤-𝒰
-- |> its single inhabitant is called |tt : Sort-Sim|.
--
-- |> The function symbols of |Σ-Sim| can be conveniently
--   defined using a data type. That is, the type family [..]
data Con-Sim : List Sort-Sim → Sort-Sim → 𝒰 ℓ₀ where
  -- |> is defined with the following constructors,
  --    all the sorts are necessarily |tt|:
  -- | - Two function symbols with an empty list of inputs [...,]
  ℕᵗ 𝔹ᵗ : Con-Sim [] tt
  -- | - and a function symbol with two inputs [....]
  ⇒₂ᵗ : Con-Sim (tt ∷ tt ∷ []) tt

-- #Notation/Rewrite# ⇒₂ᵗ = ⇒ᵗ

-- |: {}

-- [Remark]
-- | We use the same constructor names as in the definition
--   of |Ty-Sim|, but note that in this case the constructor |⇒ᵗ|
--   does not take any arguments. Instead, it is claimed in its
--   type that it has to be interpreted as having
--   two inputs.

-- //

-- [Hide]
instance
  isDiscrete:Con-Sim : ∀{xs : List Sort-Sim} {x : Sort-Sim} -> isDiscrete (Con-Sim xs x)
  isDiscrete:Con-Sim {xs} {x} = record { _≟-Str_ = lem-1 }
    where
      lem-1 : (a b : Con-Sim xs x) → Decision (a ≡-Str b)
      lem-1 ⇒₂ᵗ ⇒₂ᵗ = yes refl-≣
      lem-1 ℕᵗ ℕᵗ = yes refl-≣
      lem-1 ℕᵗ 𝔹ᵗ = no (λ ())
      lem-1 𝔹ᵗ ℕᵗ = no (λ ())
      lem-1 𝔹ᵗ 𝔹ᵗ = yes refl-≣

-- //

-- | Finally, we construct the signature [..] by setting [....]
Σ-Sim : 𝒯FOSignature ℓ₀
Σ-Sim = record { Sort = Sort-Sim ; Con = Con-Sim }


-- [Hide]
infixr 30 _⇒_
pattern _⇒_ a b = con ⇒₂ᵗ (incl a ⋆-⧜ (incl b ⋆-⧜ ◌-⧜))
pattern ℕ = con ℕᵗ ◌-⧜
pattern 𝔹 = con 𝔹ᵗ ◌-⧜

-- //



