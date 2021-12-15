
module Verification.Core.Theory.Std.Specific.FirstOrderTerm.Unification.SolutionSketch where

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

open import Verification.Core.Data.Language.HindleyMilner.Variant.Classical.Typed.Imports hiding (unify ; [_])

open import Verification.Core.Data.Language.HindleyMilner.Variant.Classical.Typed.Type.Properties
private variable μs νs : 𝐒𝐮𝐛𝐬𝐭-FO Σ-Sim

-- [Hide]
∑' = ∑_
infixl 5 ∑'
syntax ∑' (λ x -> P) = ∑[ x ] P

postulate
  here : ∀{A : 𝒰 𝑖} -> Text -> A

_[_] : ∀{αs βs : 𝐒𝐮𝐛𝐬𝐭-FO Σ-Sim} -> 𝒯⊔Term Σ-Sim ⟨ αs ⟩ tt ->  αs ⟶ βs -> 𝒯⊔Term Σ-Sim ⟨ βs ⟩ tt
_[_] = λ τ σ -> τ ⇃[ σ ]⇂
-- //

-- ==* A sketch of a solution
-- | Based on the problem description above, we present a simplified
--   unification algorithm --- again using terms from |𝒯⊔Term Σ-Sim| for
--   the sake of concreteness. A very similar definition can already be found in
--   the original paper on categorical unification of \citeauthor{UnifyCat:RydeheardBurstall:1986}.
--   The same general approach, yet formulated differently, is the one taken
--   by \citet{UnifyForm:McBride:2000}.
--
-- | The algorithm has the following type [...,]
{-# TERMINATING #-}
unify : (t s : 𝒯⊔Term Σ-Sim ⟨ μs ⟩ tt) -> Maybe (∑[ νs ] (μs ⟶ νs))
-- |> taking the terms |t| and |s|, both with variables from |μs| and returning
--   a new list of variables |νs|, as well as a substitution |μs ⟶ νs|.
--   The intention is that this substitution should be the most general unifier
--   of |t| and |s|.
-- | An implementation in terms of recursion on both arguments is very
--   natural: Compare the topmost constructors; If either
--   of them is a variable, we are done. Otherwise they must both be
--   arrows, then recurse on their arguments.
-- | It is customary to denote the cases involving variables by /flex/
--   and the ones involving constructors by /rigid/, relating to the fact
--   that variables can be changed by substitutions, while constructors cannot.
-- | We examine the cases in more detail REF.
-- | - The flex-flex case.
unify (var α) (var β) = {!!}
-- |> Here we need to check whether |α ≡ β| holds: if both
--    variables are the same, the most general unifier
--    is the identity substitution. Otherwise we return a substitution
--    which maps |α| and |β| to the same variable; |νs| contains
--    one variable less than |μs|.

-- | - The rigid-flex cases.
unify (ℕ) (var β) = {!!}
unify (𝔹) (var β) = {!!}
unify (t₀ ⇒ t₁) (var β) = {!!}

-- |> When the rigid term is a constant without arguments, the
--    mgu is straightforward: substitute the variable |β| with that type constant.
--    If it is a term with arguments, the result depends on whether
--    the variable |β| occurs in either of |t₀| or |t₁|. If it does not,
--    proceed by substituting |β| like before. If it does, the result is that
--    no unifier exists. Intuitively, this is so because if we were to
--    substitute |β| by the term on the left hand side, that term,
--    itself containing |β|, would change as well. Meaning
--    that |(t₀ ⇒ t₁) [ σ ] ≠ β [ σ ]|.

-- [Hide]
unify (var α) (ℕ) = {!!}
unify (var α) (𝔹) = {!!}
unify (var α) (t₀ ⇒ t₁) = {!!}
-- //

-- | - The rigid-rigid case.

-- [Hide]
unify (𝔹) (𝔹) = {!!}
unify (ℕ) (𝔹) = {!!}
unify (𝔹) (ℕ) = {!!}
unify (ℕ) (ℕ) = {!!}
unify (𝔹) (s₀ ⇒ s₁) = {!!}
unify (ℕ) (s₀ ⇒ s₁) = {!!}
unify (t₀ ⇒ t₁) (𝔹) = {!!}
unify (t₀ ⇒ t₁) (ℕ) = {!!}
-- //

-- |> We ignore the sub-cases where either of the inputs are
--   type constants: the mgu is the identity substitution
--   if both inputs are the same, or it does not exist if they are
--   different.
-- | Instead, focus on the case where both inputs are arrows:

unify (t₀ ⇒ t₁) (s₀ ⇒ s₁) with unify t₀ s₀
... | nothing = nothing
... | just (νs₀ , σ₀) with unify (t₁ [ σ₀ ]) (s₁ [ σ₀ ])
... | nothing = nothing
... | just (νs₁ , σ₁) = just (νs₁ , σ₀ ◆ σ₁)

-- |> The reasoning behind this implementation is the following:
--   we want to solve the unification problem by solving the partial problems
--   of |t₀ ≟ t₁| and |s₀ ≟ s₁|, and then combining their solutions.
--   But as shown in the previous example,
--   the results of these partial solutions may influence each other.
--   If a variable is substituted in one branch of the execution, that must be taken
--   into account in the other branch, where that same variable may have
--   another occurence.
-- | The solution is remarkably simple: we solve the subproblems sequentially.
--   As seen in the implementation above, we first unify |t₀| and |t₁|.
--   If these terms have no mgu (the result is |nothing|),
--   than neither does our original pair (we also return |nothing|).
--   The crux of the algorithm is the case where unification of |t₀| and |s₀|
--   succeeds: The mgu of this pair is applied to both |t₁| and |s₁|
--   before these are unified. Afterwards, the only thing left is to compose the
--   two substitutions if successful, or return |nothing| if not.
-- |: Unfortunately, a verification of this implementation for the rigid-rigid
--   case is not immediate. The two problems that arise are:
-- | 1. Correctness needs to be shown. This is, in fact, the content of the "optimist's
--   lemma".
-- | 2. Termination of the algorithm is not obvious. When |unify| is
--      called the second time, its arguments have the substitution |σ₀|
--      applied. Such a substitution usually increases the size of terms,
--      which makes it unclear whether the resulting chain of recursive calls
--      ever terminates. In Agda, this problem is visible immediately,
--      as the termination checker complains about not being able to show termination.

-- |: {}

-- | A verification of the other cases, flex-flex and rigid-flex,
--   is of course also required. In the present formalization this
--   takes a rather traditional form, as for example described in REF.
--   Most of the rest of
--   this chapter therefore is devoted to describing the correctness and
--   termination of the rigid-rigid case in a purely categorical setting,
--   as well as to the translation of that proof back to
--   the concrete category of substitutions of first order terms.


