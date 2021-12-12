
module Verification.Core.Data.Language.HindleyMilner.Variant.Classical.Typed.Type.Definition where


open import Verification.Conventions hiding (ℕ ; _⊔_)


open import Verification.Core.Data.Language.HindleyMilner.Variant.Classical.Typed.Imports
open import Verification.Core.Data.Language.HindleyMilner.Helpers
open import Verification.Core.Data.Language.HindleyMilner.Type.Variant.FreeFiniteCoproductTheoryTerm.Signature



-- [Notation]
-- | We write |ℒHMType| for a term in that signature, i.e.:
ℒHMType : (Γ : 人ℕ) -> 𝒰₀
ℒHMType Γ = 𝒯⊔Term 𝒹 Γ tt
-- //

-- [Notation]
-- | We denote the category of type substitutions by:
ℒHMTypesᵘ : 𝒰₀
ℒHMTypesᵘ = ⧜𝐒𝐮𝐛𝐬𝐭 (𝒯⊔term 𝒹)

macro ℒHMTypes = #structureOn ℒHMTypesᵘ

-- //

