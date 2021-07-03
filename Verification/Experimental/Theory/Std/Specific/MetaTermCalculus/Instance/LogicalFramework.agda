
module Verification.Experimental.Theory.Std.Specific.MetaTermCalculus.Instance.LogicalFramework where

open import Verification.Experimental.Conventions hiding (Structure)
open import Verification.Experimental.Category.Std.Category.Definition
open import Verification.Experimental.Category.Std.Functor.Definition
open import Verification.Experimental.Data.Universe.Everything
open import Verification.Experimental.Algebra.Monoid.Definition
open import Verification.Experimental.Algebra.MonoidAction.Definition
open import Verification.Experimental.Order.Lattice
open import Verification.Experimental.Category.Std.Category.Structured.Monoidal.Definition
open import Verification.Experimental.Theory.Std.Specific.MetaTermCalculus.Definition
open import Verification.Experimental.Theory.Std.Generic.TypeTheory.Simple
open import Verification.Experimental.Theory.Std.Generic.TypeTheory.Definition
open import Verification.Experimental.Theory.Std.Generic.LogicalFramework.Definition
open import Verification.Experimental.Theory.Std.TypologicalTypeTheory.CwJ

-----------------------------------
-- ==* MTC signatures


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


private
  U : CwJ (𝑘 , 𝑖 , 𝑗 , _) -> MetaTermCalculus (𝑖 , 𝑖)
  U 𝒞 = record
          { MetaKind = JKind {{of 𝒞}}
          ; varzero = {!!}
          ; varsuc = {!!}
          ; isHiddenMeta = const ⊥
          ; TermCon = iFam (JObj {{of 𝒞}})
          }


  F : MetaTermCalculus 𝑖 -> CwJ _
  F γ = Ctx-⦿ (MetaJ (MetaKind γ)) since (isCwJ:Ctx-MTC {γ = γ})
    where open MTCDefinitions γ



instance
  isLogicalFramework:MTC : isLogicalFramework (CwJ (_ , _ , _ , 𝑖)) (MTC (_ , 𝑖))
  isLogicalFramework.LFTerm isLogicalFramework:MTC = F
  isLogicalFramework.LFSig isLogicalFramework:MTC = U
  isLogicalFramework.isFunctor:LFTerm isLogicalFramework:MTC = {!!}
  isLogicalFramework.isFunctor:LFSig isLogicalFramework:MTC = {!!}
  isLogicalFramework.⟦ isLogicalFramework:MTC ⟧ = {!!}


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
--   isLogicalFramework.Term isLogicalFramework:MetaTermCalculus = {!!}
--   isLogicalFramework.Sig isLogicalFramework:MetaTermCalculus = {!!}
--   isLogicalFramework.isFunctor:Term isLogicalFramework:MetaTermCalculus = {!!}
--   isLogicalFramework.isFunctor:Sig isLogicalFramework:MetaTermCalculus = {!!}
--   isLogicalFramework.⟦ isLogicalFramework:MetaTermCalculus ⟧ = {!!}


-}

