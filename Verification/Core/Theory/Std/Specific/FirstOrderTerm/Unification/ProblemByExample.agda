
module Verification.Core.Theory.Std.Specific.FirstOrderTerm.Unification.ProblemByExample where

open import Verification.Conventions hiding (_⊔_ ; ℕ)

open import Verification.Core.Set.Discrete

open import Verification.Core.Algebra.Monoid.Definition

open import Verification.Core.Category.Std.Category.Subcategory.Full

open import Verification.Core.Data.Universe.Definition
open import Verification.Core.Data.Universe.Instance.Category
open import Verification.Core.Data.Substitution.Variant.Base.Definition

open import Verification.Core.Data.List.Variant.Binary.Natural
open import Verification.Core.Data.List.Variant.Binary.Definition
open import Verification.Core.Data.List.Variant.Binary.Element.Definition
open import Verification.Core.Data.List.VariantTranslation.Definition
open import Verification.Core.Data.List.Dependent.Variant.Binary.Definition

open import Verification.Core.Theory.Std.Specific.FirstOrderTerm.Signature
open import Verification.Core.Theory.Std.Specific.FirstOrderTerm.Definition
open import Verification.Core.Theory.Std.Specific.FirstOrderTerm.Substitution.Definition
open import Verification.Core.Data.Language.HindleyMilner.Type.Variant.FirstOrderTerm.Signature
open import Verification.Core.Data.Language.HindleyMilner.Type.VariantTranslation.Definition
open import Verification.Core.Data.Language.HindleyMilner.Type.Variant.Direct.Definition


-- ==* Stating the problem
-- | We first describe the problem of unification, and describe a typical algorithm.
--   A standard textbook is for example REF.
--   To be concrete, we use our simple types, given by |𝒯⊔Term Σ-Sim|.
-- | Let [][..] be a list of three type variables\footnote{Using Agda's ability to overload natural number constants, and the fact that |⋆List Sort-Sim ≡ 人ℕ|, this is actually valid code.}
μs : ⋆List Sort-Sim
μs = 3

-- |> and denote these variables by |α|, |β| and |γ| using patterns.

-- [Hide]
pattern α = left-∍ incl
pattern β = right-∍ (left-∍ incl)
pattern γ = right-∍ (right-∍ (left-∍ incl))
-- //

-- |> Now assume we are given two terms [..], defined by:
τ₀ τ₁ : 𝒯⊔Term Σ-Sim μs tt

τ₀ = var α ⇒ var β
τ₁ = var γ ⇒ (var α ⇒ var γ)

-- |> The task of unification is to find a substitution |σ : μs ⟶ νs|
--    into a possibly different list of type variables |νs|
--    such that |τ₀ [σ] ≡ τ₁ [σ]| holds. One such possibility is:
σ : 𝒯⊔Subst Σ-Sim μs 0
σ _ α = ℕ
σ _ β = ℕ ⇒ ℕ
σ _ γ = ℕ

-- |> Then we have, writing |[ σ ] τ| [][] for substitution:
_[_] : ∀{αs βs} -> 𝒯⊔Term Σ-Sim αs tt -> 𝒯⊔Subst Σ-Sim αs βs -> 𝒯⊔Term Σ-Sim βs tt
_[_] = λ τ σ -> subst-𝒯⊔Term Σ-Sim σ τ

_ : τ₀ [ σ ] ≡ τ₁ [ σ ]
_ = refl-≡

-- |> Both sides of the equality evalute to |ℕ ⇒ (ℕ ⇒ ℕ)|.
--   Now, even though this is a valid solution to the problem
--   of unifying |τ₀| and |τ₁|, it is not the most general one.
--   Comparing them, there is no reason at all to introduce the
--   type constant |ℕ|. The most general solution would be:
τ₌ : 𝒯⊔Term Σ-Sim 1 tt
τ₌ = var α ⇒ (var α ⇒ var α)

-- |> This can be seen by comparing subterms of |τ₀| and |τ₁|.
--   From the left hand side of the topmost arrow constructor of
--   both terms we see that |var α [ σ ] ≡ var γ [ σ ]| has to hold.
--   The right hand side requires |var β [ σ ] ≡ (var α ⇒ var γ) [ σ ]|.
--   Combining both equations, it is clear that only a single variable
--   can remain in the solution, which is given by |τ₌|.

-- | \medskip

-- | Formally, a /most general unifier/ of |τ₀| and |τ₁| is defined as a
--   substitution |σ : μs ⟶ νs|, such that:
-- | - It solves the problem, i.e., |τ₀ [ σ ] ≡ τ₁ [ σ ]|.
-- | - It is the most general solution. Which can be expressed
--     by saying that it needs to be minimal: Every other solution |σ'| which also
--     solves the problem has to factor through |σ|. Concretely, for any |σ' : μs ⟶ νs'|
--     which also unifies |τ₀| and |τ₁|, there should exist a map |ϕ : νs ⟶ νs'|,
--     such that |σ ◆ ϕ ≡ σ'|. That is, |σ| only does the work which
--     /every/ solution absolutely needs to do.
-- |: When we consider terms as substitutions, the above definition
--   is almost literally the same as the definition of a coequalizer
--   of the arrows |τ₀ τ₁ : 1 ⟶ μs| in the category of substitutions.
--   The only thing missing here is the requirement that the factoring map |ϕ|
--   needs to be unique, or equivalently, that |σ| is epi.
--   It can be easily seen that in our category of interest a most general unifier
--   is automatically epi. Such a remark may also be found in \cite{UnifyCat:Goguen:1989},
--   together with the warning that this is not necessarily the case in other relevant categories.
--   Nevertheless, as it has no relevance for the present work, we identify these two concepts.


