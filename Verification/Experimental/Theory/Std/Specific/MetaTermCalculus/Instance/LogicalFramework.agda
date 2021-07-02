
module Verification.Experimental.Theory.Std.Specific.MetaTermCalculus.Instance.LogicalFramework where

open import Verification.Experimental.Conventions hiding (Structure)
open import Verification.Experimental.Category.Std.Category.Definition
open import Verification.Experimental.Data.Universe.Everything
open import Verification.Experimental.Algebra.Monoid.Definition
open import Verification.Experimental.Algebra.MonoidAction.Definition
open import Verification.Experimental.Order.Lattice
open import Verification.Experimental.Category.Std.Category.Structured.Monoidal.Definition
-- open import Verification.Experimental.Theory.Std.Specific.MetaTermCalculus.Definition
open import Verification.Experimental.Theory.Std.Generic.TypeTheory.Simple
open import Verification.Experimental.Theory.Std.Generic.TypeTheory.Definition
open import Verification.Experimental.Theory.Std.Generic.LogicalFramework.Definition

-----------------------------------
-- ==* MTC signatures

data MetaSort : 𝒰₀ where
  main var special : MetaSort

module _ (K : 𝒰 𝑖) where
  --- basic definitions

  data Type' : 𝒰 𝑖 where
    kind : K -> Type'
    _⇒_ : Type' -> Type' -> Type'

  infixr 30 _⇒_

  data MetaJ : 𝒰 𝑖 where
    _◀_ : Jdg-⦿ Type' -> MetaSort -> MetaJ

  -- data isKindSCtx : SCtx Type' -> 𝒰 𝑖 where
  --   [] : isKindSCtx []
  --   _,,_ : ∀ k {Γ} -> isKindSCtx Γ -> isKindSCtx (Γ ,, kind k)

  -- data isKindMetaJ : MetaJ -> 𝒰 𝑖 where
  --   _◀_ : ∀{Γ} -> isKindSCtx Γ -> ∀ k s -> isKindMetaJ (Γ ⊢ kind k ◀ s)

  -- KindMetaJ = ∑ isKindMetaJ

  -- data isConArg : Type' -> 𝒰 𝑖 where
  --   kind : ∀ k -> isConArg (kind k)
  --   _⇒_ : ∀ k {a} -> isConArg a -> isConArg (kind k ⇒ a)

  -- data isConType : Type' -> 𝒰 𝑖 where
  --   kind : ∀ k -> isConType (kind k)
  --   _⇒_ : ∀ {a t} -> isConArg a -> isConType t -> isConType (a ⇒ t)


-----------------------------------
-- rule boundaries

-- module _ (K : 𝒰 𝑖) where

--   JObjT : 𝒰 𝑖
--   JObjT = Judgement (SCtx K) K

--   JBoundaryT : 𝒰 𝑖
--   JBoundaryT = Judgement (SCtx (JObjT)) JObjT

module _ {K : 𝒰 𝑖} {𝒞 : 𝒰 _} {{_ : 𝒞 is MonoidalCategory 𝑗}} where
  -- iSO : (JObjT K -> 𝒞) -> SCtx (JObjT K) -> 𝒞
  -- iSO f X = {!!}

  -- appendC : SCtx (K) -> JBoundaryT (K) -> JBoundaryT (K)
  -- appendC Δ (fst₁ ⊢ snd₁) = {!!}

  rec-𝖱-⦿ : (Jdg-⦿ K -> 𝒞) -> Rule-⦿ K -> 𝒰 _
  rec-𝖱-⦿ f (βs ⊩ β₀) = rec-Ctx-⦿ f βs ⟶ f β₀

  iFam : (Jdg-⦿ K -> 𝒞) -> Rule-⦿ K -> 𝒰 _
  iFam f β = ∀(Δ : Ctx-⦿ K) -> rec-𝖱-⦿ f (Δ ↷ β)


-----------------------------------
-- ==* MTC signatures


record MetaTermCalculus (𝑖 : 𝔏 ^ 2): 𝒰 (𝑖 ⁺) where
  field MetaKind : 𝒰 (𝑖 ⌄ 0)
  field varzero : MetaKind
  field varsuc : MetaKind
  -- field isGoodType : Type' MetaKind -> 𝒰₀
  field isHiddenMeta : MetaJ MetaKind -> 𝒰 (𝑖 ⌄ 0)
  field TermCon : (τ : Rule-⦿ MetaKind) -> 𝒰 (𝑖 ⌄ 1)

-----------------------------------
-- ==* judgement categories


record hasJudgements 𝑗 (𝒞 : MonoidalCategory 𝑖) : 𝒰 (𝑗 ⁺ ､ 𝑖) where
  field JKind : 𝒰 𝑗
  field JObj : Jdg-⦿ JKind -> ⟨ 𝒞 ⟩
  -- field JHom : (β : JBoundaryT JKind) -> iFam JObj β

open hasJudgements {{...}} public

CategoryWithJudgements : ∀ (𝑖 : 𝔏 ^ 4) -> _
CategoryWithJudgements 𝑖 = MonoidalCategory (𝑖 ⌄ 0 ⋯ 2) :& hasJudgements (𝑖 ⌄ 3)

instance
  isCategory:CategoryWithJudgements : ∀{𝑖} -> isCategory {ℓ₀ , ℓ₀} (CategoryWithJudgements 𝑖)
  isCategory:CategoryWithJudgements = {!!}

CwJ = CategoryWithJudgements

module _ {𝒞 : 𝒰 _} {{_ : 𝒞 is CwJ 𝑖}} where
  ▼₁ : Rule-⦿ JKind -> 𝒰 _
  ▼₁ = rec-𝖱-⦿ JObj

private
  U : CwJ 𝑖 -> MetaTermCalculus _
  U 𝒞 = record
          { MetaKind = JKind
          ; varzero = {!!}
          ; varsuc = {!!}
          ; isHiddenMeta = const ⊥
          ; TermCon = iFam JObj
          }


  F : MetaTermCalculus 𝑖 -> CwJ _
  F Σ = {!!}


{-

-- instance
--   isCategory:MetaTermCalculus : isCategory (ℓ₀ , ℓ₀) (MetaTermCalculus)
--   isCategory.Hom' isCategory:MetaTermCalculus = {!!}
--   isCategory.isSetoid:Hom isCategory:MetaTermCalculus = {!!}
--   isCategory.id isCategory:MetaTermCalculus = {!!}
--   isCategory._◆_ isCategory:MetaTermCalculus = {!!}
--   isCategory.unit-l-◆ isCategory:MetaTermCalculus = {!!}
--   isCategory.unit-r-◆ isCategory:MetaTermCalculus = {!!}
--   isCategory.unit-2-◆ isCategory:MetaTermCalculus = {!!}
--   isCategory.assoc-l-◆ isCategory:MetaTermCalculus = {!!}
--   isCategory.assoc-r-◆ isCategory:MetaTermCalculus = {!!}
--   isCategory._◈_ isCategory:MetaTermCalculus = {!!}

-- macro
--   𝐌𝐓𝐂 = #structureOn MetaTermCalculus


-- instance
--   isLogicalFramework:MetaTermCalculus : isLogicalFramework (𝐌𝐨𝐧𝐂𝐚𝐭 _) 𝐌𝐓𝐂
--   isLogicalFramework.Free isLogicalFramework:MetaTermCalculus = {!!}
--   isLogicalFramework.Forget isLogicalFramework:MetaTermCalculus = {!!}
--   isLogicalFramework.isFunctor:Free isLogicalFramework:MetaTermCalculus = {!!}
--   isLogicalFramework.isFunctor:Forget isLogicalFramework:MetaTermCalculus = {!!}
--   isLogicalFramework.⟦ isLogicalFramework:MetaTermCalculus ⟧ = {!!}


-}

