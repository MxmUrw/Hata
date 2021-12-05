
module Verification.Core.Theory.Std.TypologicalTypeTheory.CwJ.Specific.LayeredType where

open import Verification.Core.Conventions hiding (Structure)
open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Category.Std.Functor.Definition
open import Verification.Core.Category.Std.Natural.Definition
open import Verification.Core.Category.Std.Functor.Instance.Category
open import Verification.Core.Category.Std.Morphism.Iso
open import Verification.Core.Data.Universe.Definition
open import Verification.Core.Data.Universe.Instance.Category
open import Verification.Core.Algebra.Monoid.Definition
open import Verification.Core.Algebra.Monoid.Free
open import Verification.Core.Algebra.MonoidAction.Definition
open import Verification.Core.Order.Lattice
open import Verification.Core.Category.Std.Category.Structured.Monoidal.Definition
open import Verification.Core.Theory.Std.Generic.TypeTheory.Simple
open import Verification.Core.Theory.Std.Generic.TypeTheory.Simple.Judgement2
open import Verification.Core.Theory.Std.Generic.TypeTheory.Definition
open import Verification.Core.Theory.Std.Generic.LogicalFramework.Definition
open import Verification.Core.Theory.Std.TypologicalTypeTheory.CwJ.Definition

open import Verification.Core.Category.Std.Category.Construction.Id
open import Verification.Core.Category.Std.Functor.Instance.Monoidal

-- Layered : (K : Kinding 𝑖) (𝒞 : Category 𝑗) -> 𝒰 _
-- Layered K 𝒞 = Functor (⟨ K ⟩ since isCategory:byId) 𝒞

module _ {𝒞 : 𝒰 𝑖} {{_ : isCategory {𝑗} 𝒞}} where
  Hom:byId : ∀{a b : 𝒞} -> a ≣ b -> a ⟶ b
  Hom:byId refl-≣ = id

𝖣𝗂𝗌𝖼 : Kinding 𝑖 -> Category _
𝖣𝗂𝗌𝖼 K = (⟨ K ⟩ since isCategory:byId)

isFunctor:byFromIdCategory : ∀{A : 𝒰 𝑖} {𝒞 : Category 𝑗} {f : A -> ⟨ 𝒞 ⟩} -> isFunctor (A since isCategory:byId) 𝒞 f
isFunctor.map isFunctor:byFromIdCategory              = λ {refl-≣ → id}
isFunctor.isSetoidHom:map isFunctor:byFromIdCategory  = record { cong-∼ = λ {refl-≣ → refl }}
isFunctor.functoriality-id isFunctor:byFromIdCategory = refl
isFunctor.functoriality-◆ isFunctor:byFromIdCategory {f = refl-≣} {refl-≣} = unit-2-◆ ⁻¹


module _ {K : Kinding 𝑖} {𝒞 : Category 𝑗} {{_ : isMonoidal 𝒞}} (ι : ⟨ K ⟩ -> ⟨ 𝒞 ⟩) where

  Ks = List ⟨ K ⟩

  CKs : Category _
  CKs = Ks since isCategory:byId

  private
    emb : ⟨ K ⟩ -> 𝐅𝐮𝐧𝐜 CKs 𝒞
    emb k = f since P
      where
        f : List ⟨ K ⟩ -> ⟨ 𝒞 ⟩
        f xs = rec-List ι xs ⊗ ι k

        P = isFunctor:byFromIdCategory


    act : List ⟨ K ⟩ → Functor CKs 𝒞 → Functor CKs 𝒞
    act xs F = g since isFunctor:byFromIdCategory
      where
        g = (λ ys → ⟨ F ⟩ (ys ⋆ xs))

    lem-1 : {x y : List ⟨ K ⟩} -> {F : Functor CKs 𝒞} -> act (x ⋆ y) F ∼ act x (act y F)
    lem-1 {x} {y} {F} = α since P
      where
        α : Natural (act (x ⋆ y) F) (act x (act y F))
        α = (λ {z} -> map (assoc-l-⋆ {a = z} {x} {y} ⁻¹)) since {!!}

        P = {!!}

    instance
      hasAction-l:K-Layered : hasAction-l ′ List ⟨ K ⟩ ′ ′ Functor CKs 𝒞 ′
      hasAction-l._↷_ hasAction-l:K-Layered       = act
      hasAction-l.assoc-l-↷ hasAction-l:K-Layered {x} {y} {F} = lem-1 {x} {y} {F}
      hasAction-l._≀↷≀_ hasAction-l:K-Layered     = {!!}


  isCwJ:Layered : isCwJ K (𝐅𝐮𝐧𝐜 CKs 𝒞)
  isCwJ.⊦ isCwJ:Layered                    = emb
  isCwJ.hasAction-l:K isCwJ:Layered        = hasAction-l:K-Layered
  isCwJ.hasDistrAction-l:K isCwJ:Layered   = {!!}
  isCwJ.isFunctor:CwJAction isCwJ:Layered  = {!!}
  isCwJ.varProj isCwJ:Layered              = {!!}
  isCwJ.varSkip isCwJ:Layered              = {!!}


-- record Layered (K : Kinding 𝑖) (𝒞 : Category 𝑗) : 𝒰 (𝑖 ⊔ (𝑗 ⌄ 0)) where
--   field layer : List ⟨ K ⟩ -> ⟨ 𝒞 ⟩

-- open Layered public

-- module _ {K : Kinding 𝑖} {𝒞 : Category 𝑗} where
--   instance
--     Index-Notation:Layered : Index-Notation (Layered K 𝒞) (const (List ⟨ K ⟩)) (const (⊤-𝒰 {ℓ₀})) (const ⟨ 𝒞 ⟩)
--     Index-Notation._⌄_ Index-Notation:Layered = λ A Γ -> layer A Γ

-- module _ {K : Kinding 𝑖} {𝒞 : Category 𝑗} where
--   record LayeredHom (A B : Layered K 𝒞) : 𝒰 (𝑖 ､ 𝑗) where
--     field layer : (Γ : List ⟨ K ⟩) -> A ⌄ Γ ⟶ B ⌄ Γ


--   open LayeredHom public




