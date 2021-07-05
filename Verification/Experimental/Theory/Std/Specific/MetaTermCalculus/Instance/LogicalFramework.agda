
module Verification.Experimental.Theory.Std.Specific.MetaTermCalculus.Instance.LogicalFramework where

open import Verification.Experimental.Conventions hiding (Structure ; _◀)
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
  U : CwJ (𝑘 , 𝑖 , 𝑗 , 𝑙) -> MetaTermCalculus (𝑙 , 𝑖)
  U 𝒞 = record
          { MetaKind = JKind {{of 𝒞}}
          -- ; varzero = {!!}
          -- ; varsuc = {!!}
          ; ∂ₘᵇ = {!!}
          ; isHiddenMeta = const ⊥
          ; TermCon = iFam (JObj {{of 𝒞}})
          }



  F : ∀{𝑖} -> MetaTermCalculus 𝑖 -> CwJ _
  F γ = Ctx-MTC γ since (isCwJ:Ctx-MTC {γ = γ})
    where open MTCDefinitions γ



  i : ∀{γ : MetaTermCalculus (𝑖 , 𝑖)} -> ∀ {m} -> (Hom γ (U m)) -> (Hom (F γ) m)
  i {γ = γ} {m} ϕ = f since isFunctor:f
    where
      f : ⟨ F γ ⟩ -> ⟨ m ⟩
      f (incl x) = rec-Ctx-⦿ (λ 𝔧 -> JObj (map-Jdg-⦿ ⟨ ϕ ⟩ 𝔧)) x

      open MTCDefinitions γ

      mutual
        map-f₀-var : ∀{a b} ->
                (_⊩ᶠ↓_)
                -- (map-Ctx-⦿ (λ 𝔧 -> map-Jdg-⦿ kind 𝔧 ◀ main) ⟨ a ⟩)
                (map-Ctx-⦿ (map-Jdg-⦿ kind) ⟨ a ⟩)
                ((map-Jdg-⦿ kind) b ◀ var) →
                Hom (f a) (f (incl ([] ,, b)))

        map-f₀-var {a} {[] ⊢ α} (getapp ())
        map-f₀-var {a} {(G ,, x) ⊢ α} (MTCDefinitions.getapp ())
        map-f₀-var {a} {(G ,, x) ⊢ α} (suc te te₁) = {!!}
        map-f₀-var {a} {(G ,, x) ⊢ .x} (zero te) = {!!}
          -- let y1 = map-f₀ te
          -- in y1 ◆ {!!}
        -- map-f₀-var {a} {[] ⊢ α} (getapp x) = {!!}
        -- map-f₀-var {a} {(Γ ,, β) ⊢ α} (getapp (meta x)) = {!!}
        -- map-f₀-var {a} {(Γ ,, β) ⊢ α} (suc x x₁) = {!!}
        -- map-f₀-var {a} {(Γ ,, β) ⊢ .β} (zero (getapp (meta (skip x)))) = {!!}
        -- map-f₀-var {incl as} {(Γ ,, β) ⊢ .β} (zero (getapp (meta (give x x₁)))) = {!!}

        map-f₀-app : ∀{a b} ->
                (_⊩ᶠ↓-app_)
                (map-Ctx-⦿ (map-Jdg-⦿ kind) ⟨ a ⟩)
                -- (map-Ctx-⦿ (λ 𝔧 -> map-Jdg-⦿ kind 𝔧 ◀ main) ⟨ a ⟩)
                ((map-Jdg-⦿ kind) b ◀ main) →
                Hom (f a) (f (incl ([] ,, b)))
        map-f₀-app {a} {b} (MTCDefinitions.app (MTCDefinitions.app x x₂) x₁) = {!!}
        map-f₀-app {a} {b} (MTCDefinitions.app (MTCDefinitions.var x) x₁) = {!!}
        map-f₀-app {a} {b} (MTCDefinitions.app (MTCDefinitions.con x x₂) x₁) = let y = map-f₀ x₁ {!!}
                                                                               in {!!}
        map-f₀-app {a} {b} (MTCDefinitions.app (MTCDefinitions.meta x) x₁) = {!!}
        map-f₀-app {a} {b} (var x) = map-f₀-var x
        map-f₀-app {a} {b} (MTCDefinitions.con {_} {ts ⊩ t} {.(kind (Jdg-⦿.snd b))} x x₁) = {!!}
        map-f₀-app {a} {b} (meta x) = {!!}

        -- assign-r : Ctx-⦿ K

        map-f₀ : ∀{a b τ α} ->
                (_⊩ᶠ↓_)
                (map-Ctx-⦿ (map-Jdg-⦿ kind) ⟨ a ⟩)
                -- ((map-Jdg-⦿ kind) b ◀ main) →
                ((map-Ctx-⦿ kind) b ⊢ α ◀ main) →
                (⟦ τ ⟧-J ≣ α) ->
                Hom (f a) (f (incl ([] ,, b ↷ τ)))
        map-f₀ {a} {b} {G ⊢ t} {(α ⇒ β)} (MTCDefinitions.lam x) p with arrify-J-split {G} p
        ... | Γ' , α' , (refl-≣ , refl-≣) , r = let y = map-f₀ {τ = Γ' ⊢ t} x r
                                                in y ◆ {!!}
        map-f₀ {a} {b} {G ⊢ t} {.(kind _)} (MTCDefinitions.getapp x) p with arrify-J-kind {G} p
        ... | (refl-≣ , refl-≣) = map-f₀-app x
        -- map-f₀ {a} {b} (getapp x) = map-f₀-app x
      -- map-f₀ {a} {([] ⊢ α)} (getapp x) = {!!}
      -- map-f₀ {a} {((Γ ,, β) ⊢ α)} (getapp x) = {!!}
      -- map-f₀ {a} {((Γ ,, β) ⊢ α) ◀ var} (t) = map-f₀-var t
      -- map-f₀ {a} {((Γ ,, β) ⊢ .β) ◀ .var} (zero (getapp (meta x))) = {!!}

      map-f : ∀{a b} ->
              Sub-⦿ (MTCDefinitions._⊩ᶠ↓'_ γ)
              -- (map-Ctx-⦿ (λ 𝔧 -> map-Jdg-⦿ kind 𝔧 ◀ main) ⟨ a ⟩)
              -- (map-Ctx-⦿ (λ 𝔧 -> map-Jdg-⦿ kind 𝔧 ◀ main) ⟨ b ⟩) ->
              (map-Ctx-⦿ (map-Jdg-⦿ kind) ⟨ a ⟩)
              (map-Ctx-⦿ (map-Jdg-⦿ kind) ⟨ b ⟩) →
              Hom (f a) (f b)
      map-f = {!!}

      isFunctor:f : isFunctor ′ ⟨ F γ ⟩ ′ ′ ⟨ m ⟩ ′ f
      isFunctor.map isFunctor:f = map-f
      isFunctor.isSetoidHom:map isFunctor:f = {!!}
      isFunctor.functoriality-id isFunctor:f = {!!}
      isFunctor.functoriality-◆ isFunctor:f = {!!}


instance
  isLogicalFramework:MTC : isLogicalFramework (CwJ (_ , _ , _ , 𝑖)) (MTC (_ , 𝑖)) -- (MTC (𝑙 , (𝑖 ⊔ 𝑙)))
  isLogicalFramework.LFTerm (isLogicalFramework:MTC) = F
  isLogicalFramework.LFSig isLogicalFramework:MTC = U
  isLogicalFramework.isFunctor:LFTerm isLogicalFramework:MTC = {!!}
  isLogicalFramework.isFunctor:LFSig isLogicalFramework:MTC = {!!}
  isLogicalFramework.interp isLogicalFramework:MTC = i


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

