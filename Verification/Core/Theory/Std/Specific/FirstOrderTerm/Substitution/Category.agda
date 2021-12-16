
module Verification.Core.Theory.Std.Specific.FirstOrderTerm.Substitution.Category where

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
open import Verification.Core.Theory.Std.Specific.FirstOrderTerm.Substitution.Definition


-- | Let |Σ_FO| be a signature. The category of terms over |Σ_FO| and substitutions, is
--   denoted by |𝐒𝐮𝐛𝐬𝐭-FO|. Usually, this category is defined as the Kleisli category
--   of the term monad, but for our definition of terms it is easier to work with
--   relative monads \cite{Altenkirch_Chapman_Uustalu_2014} instead.

-- [Lemma]
-- | The category |𝐒𝐮𝐛𝐬𝐭-FO| has coproducts.

-- //

-- [Lemma]
-- | The category |𝐒𝐮𝐛𝐬𝐭-FO| has epi-mono factorizations.
--   This lemma is not fully formalized.

-- //

