
module Verification.Core.Theory.Std.Specific.FirstOrderTerm.Substitution.Definition where

open import Verification.Conventions hiding (_⊔_)

open import Verification.Core.Set.Discrete

open import Verification.Core.Algebra.Monoid.Definition

open import Verification.Core.Category.Std.Category.Subcategory.Full

open import Verification.Core.Data.Universe.Definition
open import Verification.Core.Data.Universe.Instance.Category
open import Verification.Core.Data.Substitution.Variant.Base.Definition

open import Verification.Core.Data.List.Variant.Binary.Definition
open import Verification.Core.Data.List.Variant.Binary.Element.Definition
open import Verification.Core.Data.List.VariantTranslation.Definition
open import Verification.Core.Data.List.Dependent.Variant.Binary.Definition

open import Verification.Core.Theory.Std.Specific.FirstOrderTerm.Signature
open import Verification.Core.Theory.Std.Specific.FirstOrderTerm.Definition


-- | Let [..] be a signature in this section.
module _ (Σ : 𝒯FOSignature 𝑖) where
  private variable αs βs γs : ⋆List (Sort Σ)

  -- |> Given a term |t : 𝒯⊔Term Σ βs α|, we can
  --    substitute the occurences of variables |β ∈ βs|
  --    with terms in a context |γs|, provided their sorts match.
  --    Such a /substitution from/ |βs| /to/ |γs| is encoded by the following type:

  𝒯⊔Subst : ⋆List (Sort Σ) -> ⋆List (Sort Σ) -> 𝒰 𝑖
  𝒯⊔Subst βs γs = ∀ β -> βs ∍ β -> 𝒯⊔Term Σ γs β

  -- [Remark]
  -- | One might notice that this is the same concept
  --   as used in the type of the |con| constructor in
  --   Definition REF. The only difference is that here
  --   we use dependent functions instead of dependent lists.
  --   The reason for using both of these two equivalent
  --   formulations is that the categorical
  --   structure of substitutions and coproducts therein
  --   is easier stated in terms of |𝒯⊔Subst|. However,
  --   unification of terms, being defined by induction,
  --   also requires an inductive definition of the components
  --   of terms, hence the list-based definition for |con|.

  -- //

  -- | We explicitly state the list-based formulation,
  --   denoting it by |𝒯⊔Terms|, since the focus of this version
  --   is the realization of a substitution by a list of terms.
  --   That is, we define:

  𝒯⊔Terms : ⋆List (Sort Σ) -> ⋆List (Sort Σ) -> 𝒰 𝑖
  𝒯⊔Terms βs γs = ⋆List[ β ∈ βs ] (𝒯⊔Term Σ γs β)

-- #Notation/Rewrite# 𝒯⊔Subst = Subst_{FO}
-- #Notation/Rewrite# 𝒯⊔Term = Term_{FO}
-- #Notation/Rewrite# 𝒯⊔Terms = Terms_{FO}

  -- | Using this notation, we can define how a substitution
  --   acts on terms.

  -- [Definition]
  -- | The action of a substitution |σ : 𝒯⊔Subst αs βs| on
  --   a term of type |𝒯⊔Term αs τ| is given by the following function:
  mutual
    subst-𝒯⊔Term : ∀{τ} -> 𝒯⊔Subst αs βs -> 𝒯⊔Term Σ αs τ -> 𝒯⊔Term Σ βs τ
    subst-𝒯⊔Term σ (var x)     = σ _ x
    subst-𝒯⊔Term σ (con c ts)  = con c (subst-𝒯⊔Terms σ ts)

  -- |> It is defined mutually with a second function that applies substitutions
  --   to a list of terms, as this is needed in the recursive call
  --   of the |con| case.

  -- | The version for lists merely applies the first function to all elements.

    subst-𝒯⊔Terms : ∀{αs βs τs} -> 𝒯⊔Subst αs βs -> 𝒯⊔Terms τs αs -> 𝒯⊔Terms τs βs
    subst-𝒯⊔Terms σ ◌-⧜        = ◌-⧜
    subst-𝒯⊔Terms σ (incl x)     = incl (subst-𝒯⊔Term σ x)
    subst-𝒯⊔Terms σ (t ⋆-⧜ s)  = subst-𝒯⊔Terms σ t ⋆-⧜ subst-𝒯⊔Terms σ s

-- //

-- [Remark]
-- | Note how in this definition the order of input sorts and output sorts is reversed
--   between single terms |𝒯⊔Term αs τ| and |𝒯⊔Terms τs αs|. This is because, while
--   it is natural to think of terms as functions from input sorts to an output sort,
--   substitutions are rather thought of as functions which convert terms with input sorts |αs|
--   to terms with input sorts |βs|. The type |𝒯⊔Terms τs αs| follows the convention
--   of substitutions and thus has a reversed order of parameters with respect to terms.
--   Since in the following parts substitutions play a more prominent role than terms,
--   we shall drop the previous intuition of terms as functions from now on. Instead,
--   we consider them as special kinds of substitutions. A term |t : 𝒯⊔Term αs τ|
--   is now thought of as a substitution |incl τ → αs|, substituting the single
--   variable |τ| by the value |t| containing variables from |αs|.
-- | From this point of view, actually applying a substitution |σ : αs → βs| to
--   a term |incl τ → αs| is then simply given by their composition (as defined in REF).

-- //

