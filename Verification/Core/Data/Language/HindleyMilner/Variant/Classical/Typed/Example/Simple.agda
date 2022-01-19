
module Verification.Core.Data.Language.HindleyMilner.Variant.Classical.Typed.Example.Simple where

open import Verification.Conventions hiding (ℕ ; _⊔_ ; Σ)

open import Verification.Core.Data.List.Variant.Binary.Element.Definition
open import Verification.Core.Data.List.Variant.Unary.Element
open import Verification.Core.Data.Substitution.Variant.Base.Definition

open import Verification.Core.Data.Language.HindleyMilner.Variant.Classical.Typed.Context.Definition
open import Verification.Core.Data.Language.HindleyMilner.Type.Variant.FirstOrderTerm.Signature
open import Verification.Core.Data.Language.HindleyMilner.Variant.Classical.Typed.Imports
open import Verification.Core.Data.Language.HindleyMilner.Variant.Classical.Typed.Signature
open import Verification.Core.Data.Language.HindleyMilner.Variant.Classical.Typed.Typecheck.Main
open import Verification.Core.Data.Language.HindleyMilner.Variant.Classical.Untyped.Definition
open import Verification.Core.Data.Language.HindleyMilner.Helpers
open import Verification.Core.Category.Std.RelativeMonad.KleisliCategory.Definition
open import Verification.Core.Category.Std.RelativeMonad.KleisliCategory.Instance.FiniteCoproductCategory
open import Verification.Core.Theory.Std.Specific.FirstOrderTerm.Instance.RelativeMonad
open import Verification.Core.Theory.Std.Specific.FirstOrderTerm.Instance.hasEpiMonoFactorization


infixr 30 _⇒₃_
pattern _⇒₃_ a b = con ⇒₂ᵗ (incl a ⋆-⧜ (incl b ⋆-⧜ ◌-⧜))
-- pattern ℕ = con ℕᵗ ◌-⧜
-- pattern 𝔹 = con 𝔹ᵗ ◌-⧜

oneConstant-Sim : {a : ⧜𝐒𝐮𝐛𝐬𝐭 (𝒯⊔term Σ-Sim)} -> a ⟶ ⊥
oneConstant-Sim {a} = surj-map-ι-⧜𝐒𝐮𝐛𝐬𝐭 (incl (λ {tt x → ℕ}))


instance
  isℒHMTypeCtx:𝐒𝐮𝐛𝐬𝐭𝒯⊔Term : isℒHMTypeCtx {ℓ₀ , ℓ₀} (⧜𝐒𝐮𝐛𝐬𝐭 (𝒯⊔term Σ-Sim))
  isℒHMTypeCtx.isCategory:ℒHMTypeCtx isℒHMTypeCtx:𝐒𝐮𝐛𝐬𝐭𝒯⊔Term = it
  isℒHMTypeCtx.hasCoproducts:ℒHMTypeCtx isℒHMTypeCtx:𝐒𝐮𝐛𝐬𝐭𝒯⊔Term = it
  isℒHMTypeCtx.hasUnification:ℒHMTypeCtx isℒHMTypeCtx:𝐒𝐮𝐛𝐬𝐭𝒯⊔Term = it
  isℒHMTypeCtx.hasSplitEpiMonoFactorization:ℒHMTypeCtx isℒHMTypeCtx:𝐒𝐮𝐛𝐬𝐭𝒯⊔Term = it
  isℒHMTypeCtx.∼→≡ isℒHMTypeCtx:𝐒𝐮𝐛𝐬𝐭𝒯⊔Term = ≡-Str→≡
  isℒHMTypeCtx.μκᵘ isℒHMTypeCtx:𝐒𝐮𝐛𝐬𝐭𝒯⊔Term = incl (incl tt)
  (isℒHMTypeCtx:𝐒𝐮𝐛𝐬𝐭𝒯⊔Term isℒHMTypeCtx.⇒ᵘ ⧜subst (incl f)) (⧜subst (incl g)) = ⧜subst (incl $ f ⇒₃ f)
  isℒHMTypeCtx.oneConstant isℒHMTypeCtx:𝐒𝐮𝐛𝐬𝐭𝒯⊔Term = oneConstant-Sim

Σ : ℒHMSignature _
Σ = ⧜𝐒𝐮𝐛𝐬𝐭 (𝒯⊔term Σ-Sim)

t-0 : UntypedℒHM 0
t-0 = slet (lam (var incl)) (app (var incl) (var incl))

Empty : ℒHMCtx {Σ = Σ}  [] (incl ◌)
Empty = []

result-t-0 = γ {𝒯 = ⟨ Σ ⟩} Empty t-0



