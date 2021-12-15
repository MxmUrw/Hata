
module Verification.Core.Data.Language.HindleyMilner.Type.VariantTranslation.Definition where


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
open import Verification.Core.Data.List.VariantTranslation.Definition
open import Verification.Core.Data.Substitution.Variant.Base.Definition

open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Category.Std.Morphism.Iso
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



open import Verification.Core.Data.Language.HindleyMilner.Type.Variant.Direct.Definition
open import Verification.Core.Data.Language.HindleyMilner.Type.Variant.FirstOrderTerm.Signature

-- | Next, we show that first order terms over |Σ-Sim|
--   do indeed correspond to inhabitants of the directly
--   defined type |Ty-Sim|.

-- [Lemma]
-- | Let [..] be a list of sorts.
module _ {μs : 人ℕ} where
  -- |> Then there is an isomorphism
  _ : 𝒯⊔Term Σ-Sim μs tt ≅ Ty-Sim μs
  -- |> between the two different definitions of simple terms.

-- //

-- [Proof]
-- | We show this [] by defining two inverse functions.
  _ = Proof where

    -- |> First, define:
    ϕ : 𝒯⊔Term Σ-Sim μs tt -> Ty-Sim μs
    ϕ (var i)       = var i
    ϕ (con ℕᵗ _)    = ℕᵗ
    ϕ (con 𝔹ᵗ _)    = 𝔹ᵗ
    ϕ (con ⇒₂ᵗ (incl t ⋆-⧜ (incl s ⋆-⧜ ◌-⧜))) = ϕ t ⇒ᵗ ϕ s
    -- |> In the case of the function symbol |⇒₂ᵗ|
    --    we have to unwrap its list of arguments to access
    --    the actual terms inside, and can then proceed
    --    recursively.

    -- | Next, very similarly, we define a function in
    --   the other direction:
    ϕ⁻¹ : Ty-Sim μs -> 𝒯⊔Term Σ-Sim μs tt
    ϕ⁻¹ ℕᵗ        = con ℕᵗ ◌-⧜
    ϕ⁻¹ 𝔹ᵗ        = con 𝔹ᵗ ◌-⧜
    ϕ⁻¹ (t ⇒ᵗ s)  = con ⇒₂ᵗ ((incl (ϕ⁻¹ t)) ⋆-⧜ (incl (ϕ⁻¹ s) ⋆-⧜ ◌-⧜))
    ϕ⁻¹ (var i)   = var i

    -- |> By induction it is easy to show
    --    that |ϕ⁻¹| is indeed the inverse of |ϕ|.
    -- |> We have [..][][][][]
    lem-1 : ϕ ◆ ϕ⁻¹ ≡ id
    lem-1 i (var x) = var x
    lem-1 i (con ℕᵗ ◌-⧜) = (con ℕᵗ ◌-⧜)
    lem-1 i (con 𝔹ᵗ ◌-⧜) = (con 𝔹ᵗ ◌-⧜)
    lem-1 i (con ⇒₂ᵗ (incl t ⋆-⧜ (incl s ⋆-⧜ ◌-⧜))) = (con ⇒₂ᵗ (incl (lem-1 i t) ⋆-⧜ (incl (lem-1 i s) ⋆-⧜ ◌-⧜)))

    -- |> and [..][][][][].
    lem-2 : ϕ⁻¹ ◆ ϕ ≡ id
    lem-2 i ℕᵗ = ℕᵗ
    lem-2 i 𝔹ᵗ = 𝔹ᵗ
    lem-2 i (t ⇒ᵗ s) = lem-2 i t ⇒ᵗ lem-2 i s
    lem-2 i (var x) = var x

    -- |> Thus we conclude by defining a value
    Proof : 𝒯⊔Term Σ-Sim μs tt ≅ Ty-Sim μs
    Proof = ϕ since record { inverse-◆ = ϕ⁻¹ ; inv-r-◆ = lem-1 ; inv-l-◆ = lem-2 }
    -- |> and use this as proof term in the statement
    --    of the lemma.

-- //


-- [Hide]
infixr 30 _⇒_
pattern _⇒_ a b = con ⇒₂ᵗ (incl a ⋆-⧜ (incl b ⋆-⧜ ◌-⧜))
pattern ℕ = con ℕᵗ ◌-⧜

-- //


