

module Verification.Old.Core.Algebra.Action.MonoidModule where

open import Verification.Conventions
open import Verification.Old.Core.Category.Definition
open import Verification.Old.Core.Category.Instance.Type
open import Verification.Old.Core.Algebra.Basic.Monoid

-------------------------
-- === Modules over monoids
-- | We define modules over monoids, i.e., monoid actions.

record IMonoidModule (M : Monoid 𝑖) {𝑗} (A : 𝒰 𝑗) : 𝒰 (𝑖 ⊔ 𝑗) where
  field _↷_ : ⟨ M ⟩ -> A -> A
        functoriality-𝟷 : ∀{a} -> 𝟷 ↷ a ≡ a
        functoriality-⋅ : ∀{m n} -> ∀{a} -> (m ⋅ n) ↷ a ≡ m ↷ n ↷ a
  infixr 50 _↷_

open IMonoidModule {{...}} public
_-IMonoidModule_ = IMonoidModule
unquoteDecl MonoidModule monoidModule = #struct "Mod" (quote IMonoidModule) "A" MonoidModule monoidModule
_-MonoidModule_ = MonoidModule



record IMonoidModuleHom {M : Monoid 𝑖} (A B : (M)-MonoidModule 𝑗) (f : ⟨ A ⟩ -> ⟨ B ⟩) : 𝒰 (𝑖 ⊔ 𝑗) where
  field naturality-↷ : {m : ⟨ M ⟩} -> ∀ {a} -> f (m ↷ a) ≡ m ↷ (f a)

open IMonoidModuleHom {{...}} public
unquoteDecl MonoidModuleHom monoidModuleHom = #struct "ModHom" (quote IMonoidModuleHom) "f" MonoidModuleHom monoidModuleHom

comp-MonoidModule : ∀{M : Monoid 𝑖} {A B C : (M)-MonoidModule 𝑗} -> (f : MonoidModuleHom A B) -> (g : MonoidModuleHom B C) -> MonoidModuleHom A C
⟨ comp-MonoidModule f g ⟩ = ⟨ f ⟩ ◆ ⟨ g ⟩
IMonoidModuleHom.naturality-↷ (of (comp-MonoidModule f g)) = cong ⟨ g ⟩ (naturality-↷) ∙ naturality-↷

instance
  ICategory:MonoidModule : ∀{M : Monoid 𝑖} -> ICategory ((M)-MonoidModule 𝑗) (𝑖 ⊔ 𝑗 , 𝑗)
  ICategory.Hom ICategory:MonoidModule = MonoidModuleHom
  ICategory._≣_ ICategory:MonoidModule f g = ⟨ f ⟩ ≡ ⟨ g ⟩
  IEquiv.refl (ICategory.IEquiv:≣ ICategory:MonoidModule) = refl
  IEquiv.sym (ICategory.IEquiv:≣ ICategory:MonoidModule) = sym
  IEquiv._∙_ (ICategory.IEquiv:≣ ICategory:MonoidModule) = _∙_
  ⟨ ICategory.id ICategory:MonoidModule ⟩ = id
  IMonoidModuleHom.naturality-↷ (of (ICategory.id ICategory:MonoidModule)) = refl
  ICategory._◆_ ICategory:MonoidModule = comp-MonoidModule
  ICategory._◈_ ICategory:MonoidModule p q = λ i -> (p i) ◆ (q i)
  ICategory.unit-l-◆ ICategory:MonoidModule = {!!}
  ICategory.unit-r-◆ ICategory:MonoidModule = {!!}
  ICategory.unit-2-◆ ICategory:MonoidModule = {!!}
  ICategory.assoc-l-◆ ICategory:MonoidModule = {!!}
  ICategory.assoc-r-◆ ICategory:MonoidModule = {!!}

-- instance
--   ICategory:MonoidModule : ∀{M : Monoid 𝑖} -> ICategory ((M)-MonoidModule 𝑗) (𝑖 ⊔ 𝑗 , 𝑗)
--   ICategory.ICategoryInst ICategory:MonoidModule = ICategory:MonoidModule


Category:MonoidModule : ∀(M : Monoid 𝑖) (𝑗 : 𝔏) -> Category _ -- (𝑖 ⊔ 𝑗)
Category:MonoidModule M 𝑗 = category _ {{ICategory:MonoidModule {𝑗 = 𝑗} {M = M}}}


MonoidModule:Free : ∀(M : Monoid 𝑖) -> 𝒰 𝑗 -> MonoidModule M (𝑖 ､ 𝑗)
⟨ MonoidModule:Free M A ⟩ = ⟨ M ⟩ ×-𝒰 A
IMonoidModule._↷_ (of MonoidModule:Free M A) m (n , a) = (m ⋅ n , a)
IMonoidModule.functoriality-𝟷 (of MonoidModule:Free M x) {a = (m , a)} = λ i -> (unit-l-⋅ {a = m} i , a)
IMonoidModule.functoriality-⋅ (of MonoidModule:Free M x) {m = m} {n = n} {a = (o , a)} = cong₂ _,_ assoc-⋅ refl


