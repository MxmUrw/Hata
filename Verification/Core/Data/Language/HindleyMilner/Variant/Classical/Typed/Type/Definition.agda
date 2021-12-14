
module Verification.Core.Data.Language.HindleyMilner.Variant.Classical.Typed.Type.Definition where


open import Verification.Conventions hiding (ℕ ; _⊔_)


open import Verification.Core.Data.Language.HindleyMilner.Variant.Classical.Typed.Imports
open import Verification.Core.Data.Language.HindleyMilner.Helpers
open import Verification.Core.Data.Language.HindleyMilner.Type.Variant.FirstOrderTerm.Signature

-- | Types are defined as in example ...
--   We give the following names.

-- [Notation]
-- | We write |ℒHMType| for a term in that signature, i.e.:
ℒHMType : 人ℕ -> 𝒰₀
ℒHMType μs = 𝒯⊔Term 𝒹 μs tt

-- | That is, given a list of type variables |μs : 人ℕ|,
--   an element of |ℒHMType μs| is a HM type,
--   with type variables from |μs|.

-- #Notation/Rewrite# ℒHMType = Ty_{HM}
-- //

-- [Notation]
-- | We denote the category of type substitutions by:
ℒHMTypesᵘ : 𝒰₀
ℒHMTypesᵘ = ⧜𝐒𝐮𝐛𝐬𝐭 (𝒯⊔term 𝒹)

macro ℒHMTypes = #structureOn ℒHMTypesᵘ

-- #Notation/Rewrite# ℒHMTypes = 𝐓𝐲𝐕𝐚𝐫_{HM}

-- //

-- ===* Concerning polymorphic types / type schemes
-- | The actual types a HM term can have are
--   types with quantifications, e.g. the
--   identity function has the type |∀ α. α ⇒ α|.
--   We can mirror that by saying the following:

-- [Definition]
-- | A type scheme [..] is given by the following
record ℒHMTypeScheme (μs : 人ℕ) : 𝒰₀ where
  -- | 1. A list of type variables [..] over which the type should be quantified.
  field αs : 人ℕ
  -- | 2. The actual type, allowed to use type variables from
  --      the meta variables |μs|, as well as its bound variables |αs|.
  field type : ℒHMType (μs ⋆ αs)
-- //

-- [Remark]
-- | In practice though, it turns out that such a data type is not
--   useful, for two reasons:
-- | 1. Regarding contexts, most operations only act on the free variables
--      of a type. It is convenient to have substitutions preserve the
--      quantification of the types in the context definitionally. For that,
--      a separate list of quantifications, and of types with those bound
--      variables is required.
-- | 2. Regarding the inferred type of a term, here the difference between
--      free and bound variables is not very pronounced. Since we are mainly
--      concerned with principal type schemes, given a type assignment |Γ ⊢ τ|,
--      where |τ| is simply a type with some list |μs| of type variables,
--      this list can now be split into parts |μs ≅ μsₐ ⊔ μsₓ|,
--      such that |μsₐ| represents the free variables, and |μsₓ| represents the
--      bound variables. Since we want the most general type scheme,
--      we always strive to keep |μsₐ| as small as possible. Thus, the type |τ|
--      in the aforementioned type assignment |Γ ⊢ τ| can be implicitly considered
--      to be quantified over all variables |μsₓ| which do not occur in |Γ|.

-- //





