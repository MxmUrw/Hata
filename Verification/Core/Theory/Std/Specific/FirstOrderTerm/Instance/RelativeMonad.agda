
module Verification.Core.Theory.Std.Specific.FirstOrderTerm.Instance.RelativeMonad where

open import Verification.Conventions hiding (_⊔_)

open import Verification.Core.Set.Discrete
open import Verification.Core.Set.Setoid.Definition

open import Verification.Core.Algebra.Monoid.Definition

open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Category.Std.Functor.Definition
open import Verification.Core.Category.Std.Category.Subcategory.Full
open import Verification.Core.Category.Std.RelativeMonad.Definition
open import Verification.Core.Category.Std.RelativeMonad.Finitary.Definition

open import Verification.Core.Data.Universe.Definition
open import Verification.Core.Data.Universe.Instance.Category
open import Verification.Core.Data.Substitution.Variant.Base.Definition

open import Verification.Core.Data.List.Variant.Binary.Definition
open import Verification.Core.Data.List.Variant.Binary.Element.Definition
open import Verification.Core.Data.List.Variant.Binary.Element.As.Indexed
open import Verification.Core.Data.List.VariantTranslation.Definition
open import Verification.Core.Data.List.Dependent.Variant.Binary.Definition

open import Verification.Core.Theory.Std.Specific.FirstOrderTerm.Signature
open import Verification.Core.Theory.Std.Specific.FirstOrderTerm.Definition
open import Verification.Core.Theory.Std.Specific.FirstOrderTerm.Substitution
open import Verification.Core.Theory.Std.Specific.FirstOrderTerm.Instance.Functor

open import Verification.Core.Data.Indexed.Definition
open import Verification.Core.Data.Indexed.Instance.Monoid
open import Verification.Core.Data.FiniteIndexed.Definition

module _ {𝓅 : 𝒯FOSignature 𝑖} where
  repure-𝒯⊔term : ∀{a} -> 𝑓𝑖𝑛 (Sort 𝓅) a ⟶ 𝒯⊔term 𝓅 a
  repure-𝒯⊔term i x = var x

  mutual
    reext-𝒯⊔Terms : ∀{a b αs} -> 𝑓𝑖𝑛 (Sort 𝓅) a ⟶ 𝒯⊔term 𝓅 b -> 𝒯⊔Terms 𝓅 αs ⟨ a ⟩ ⟶ 𝒯⊔Terms 𝓅 αs ⟨ b ⟩
    reext-𝒯⊔Terms f ◌-⧜ = ◌-⧜
    reext-𝒯⊔Terms f (x ⋆-⧜ y) = reext-𝒯⊔Terms f x ⋆-⧜ reext-𝒯⊔Terms f y
    reext-𝒯⊔Terms f (incl x) = incl (reext-𝒯⊔term f _ x)

    reext-𝒯⊔term : ∀{a b} -> 𝑓𝑖𝑛 (Sort 𝓅) a ⟶ 𝒯⊔term 𝓅 b -> 𝒯⊔term 𝓅 a ⟶ 𝒯⊔term 𝓅 b
    reext-𝒯⊔term f i (var x) = f i x
    reext-𝒯⊔term f i (con c x) = con c (reext-𝒯⊔Terms f x)

  instance
    isRelativeMonad:𝒯⊔term : isRelativeMonad (𝑓𝑖𝑛 (Sort 𝓅)) (𝒯⊔term 𝓅)
    isRelativeMonad.repure isRelativeMonad:𝒯⊔term = repure-𝒯⊔term
    isRelativeMonad.reext isRelativeMonad:𝒯⊔term = reext-𝒯⊔term
    isRelativeMonad.reunit-l isRelativeMonad:𝒯⊔term = {!!}
    isRelativeMonad.reunit-r isRelativeMonad:𝒯⊔term = {!!}
    isRelativeMonad.reassoc isRelativeMonad:𝒯⊔term = {!!}


module _ {Σ : 𝒯FOSignature 𝑖} where
  simpleVar : ∀{Γ : ⧜𝐒𝐮𝐛𝐬𝐭 (𝒯⊔term Σ )} {τ : Sort Σ} -> (⟨ Γ ⟩ ∍ τ) -> incl (incl τ) ⟶ Γ
  simpleVar v = ⧜subst (incl (repure _ v))


--------------------------------------
-- named definitions for the category
module _ (𝓅 : 𝒯FOSignature 𝑖) where
  open import Verification.Core.Data.Substitution.Variant.Base.Definition
  open import Verification.Core.Category.Std.Limit.Specific.Coproduct.Definition

  macro 𝐒𝐮𝐛𝐬𝐭-Sim = #structureOn (InductiveSubstitution (𝒯⊔term 𝓅))

  module Overwrite:isCategory:𝐒𝐮𝐛𝐬𝐭-Sim where
    open isCategory (isCategory:⧜𝐒𝐮𝐛𝐬𝐭 {T = 𝒯⊔term 𝓅}) public

  module Overwrite:hasCoproducts:𝐒𝐮𝐛𝐬𝐭-Sim where
    open hasCoproducts (hasCoproducts:⧜𝐒𝐮𝐛𝐬𝐭 {T = 𝒯⊔term 𝓅}) public

  module Overwrite:isCoproduct:𝐒𝐮𝐛𝐬𝐭-Sim {a b : 𝐒𝐮𝐛𝐬𝐭-Sim} where
    open isCoproduct (isCoproduct:⊔-⧜𝐒𝐮𝐛𝐬𝐭 {T = 𝒯⊔term 𝓅} {a = a} {b = b}) public

  module Overwrite:hasInitial:𝐒𝐮𝐛𝐬𝐭-Sim where
    open hasInitial (hasInitial:⧜𝐒𝐮𝐛𝐬𝐭 {T = 𝒯⊔term 𝓅}) public

  module Overwrite:isInitial:𝐒𝐮𝐛𝐬𝐭-Sim where
    open isInitial (isInitial:⊥-⧜𝐒𝐮𝐛𝐬𝐭 {T = 𝒯⊔term 𝓅}) public

  module Overwrite:hasFiniteCoproducts:𝐒𝐮𝐛𝐬𝐭-Sim where
    open hasFiniteCoproducts (hasFiniteCoproducts:⧜𝐒𝐮𝐛𝐬𝐭 {T = 𝒯⊔term 𝓅}) public

module _ {Σ : 𝒯FOSignature 𝑖} where
  module §-reext-Terms-𝕋× where
    prop-1 : ∀{a b x} -> (α β : 𝑓𝑖𝑛 (Sort Σ) (incl a) ⟶  𝒯⊔term Σ b) -> (t : 𝒯⊔Term Σ a x) -> reext α _ t ≡ reext β _ t -> ∀ i s -> α i s ≡ β i s
    prop-1 α β (var x) p i s = {!!}
    prop-1 α β (con c x) p i s = {!!}

    prop-2 : ∀{x y : ⧜𝐒𝐮𝐛𝐬𝐭 (𝒯⊔term Σ)} {αsx : ⋆List (Sort Σ)} -> (h : y ⟶ x)
             -> (tsx : CtxHom (𝒯⊔Term Σ) (αsx) ⟨ y ⟩)
             -> (reext-𝒯⊔Terms (sub-⧜𝐒𝐮𝐛𝐬𝐭 h) tsx)
               ≣
               (tsx ◆-⧜𝐒𝐮𝐛𝐬𝐭' h)
    prop-2 {x} {y} h ◌-⧜ = refl-≣
    prop-2 {x} {y} h (incl x₁) = refl-≣
    prop-2 {x} {y} h (tsx ⋆-⧜ tsy) = cong₂-Str _⋆-⧜_ (prop-2 h tsx) (prop-2 h tsy)




