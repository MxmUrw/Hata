
module Verification.Experimental.Theory.Std.Specific.MetaTermCalculus2.Instance.LogicalFramework where

open import Verification.Experimental.Conventions hiding (Structure ; _◀)
open import Verification.Experimental.Category.Std.Category.Definition
open import Verification.Experimental.Category.Std.Functor.Definition
open import Verification.Experimental.Data.Universe.Everything
open import Verification.Experimental.Algebra.Monoid.Definition
open import Verification.Experimental.Algebra.Monoid.Free
open import Verification.Experimental.Algebra.MonoidAction.Definition
open import Verification.Experimental.Order.Lattice
open import Verification.Experimental.Category.Std.Category.Structured.Monoidal.Definition
open import Verification.Experimental.Category.Std.Morphism.Iso
open import Verification.Experimental.Theory.Std.Specific.MetaTermCalculus2.Definition
open import Verification.Experimental.Theory.Std.Generic.TypeTheory.Simple
open import Verification.Experimental.Theory.Std.Generic.TypeTheory.Simple.Judgement2
open import Verification.Experimental.Theory.Std.Generic.TypeTheory.Definition
open import Verification.Experimental.Theory.Std.Generic.LogicalFramework.Definition
open import Verification.Experimental.Theory.Std.TypologicalTypeTheory.CwJ.Definition

module _ {𝒞 : 𝒰 _} {{_ : 𝒞 is Category 𝑖}} where
  infixr 10 _⟶⟨_⟩_
  _⟶⟨_⟩_ : ∀(a : 𝒞) {b c : 𝒞} -> (ϕ : a ⟶ b) -> (ψ : b ⟶ c ) -> a ⟶ c
  _⟶⟨_⟩_ _ ϕ ψ = ϕ ◆ ψ

  _⟶id : ∀(a : 𝒞) -> a ⟶ a
  _⟶id a = id


private
  module _ {K : Kinding 𝑖₁} where
    U : CwJ K (𝑘 , 𝑖₁ , 𝑗) -> MetaTermCalculus K 𝑖₁
    U 𝒞 = record {TermCon = JHom}



    F : ∀{𝑖} -> MetaTermCalculus K 𝑖 -> CwJ K _
    F γ = MTCCat γ since (isCwJ:MTCCat {γ = γ})
      where open MTCDefinitions γ



  i : ∀{K : Kinding 𝑖} {γ : MetaTermCalculus K (𝑖)} -> ∀ {ℳ} -> (Hom γ (U ℳ)) -> (Hom (F γ) ℳ)
  i {γ = γ} {ℳ} ϕ = f since isFunctor:f
    where
      instance
        _ : isSetoid ⟨ ℳ ⟩
        _ = isSetoid:byCategory

      open MTCDefinitions γ

      f : ⟨ F γ ⟩ -> ⟨ ℳ ⟩
      f (incl x) = ⟦ x ⟧

      mutual
        -- map-f₀-var : ∀{𝔍 Δ Γ α} ->
        --         𝔍 ⊩ᶠ-var (Γ ∣ Δ ⇒ α)
        --         -> Hom (⟦ Γ ↷ (𝔍 ⋆ Δ) ⟧) (⟦ Γ ↷ α ⟧)
        -- map-f₀-var (suc x x₁) = {!!}
        -- map-f₀-var (zero {𝔍} {Γ} {α} x) =
        --   let x' = map-f₀ x
        --   in ⟦ (Γ ⋆ ⦋ α ⦌) ↷ (𝔍 ⋆ []) ⟧    ⟶⟨ {!!} ⟩
        --      ⟦ (Γ ⋆ ⦋ α ⦌) ↷ ([] ⊢ α) ⟧     ⟶id

        map-f₀ : ∀{𝔍 Δ Γ α} ->
                𝔍 ⊩ᶠ (Γ ∣ Δ ⇒ α)
                -> Hom (⟦ Γ ↷ (𝔍 ⋆ Δ) ⟧) (⟦ Γ ↷ α ⟧)
        map-f₀ (meta {αs} {α}) = unit-r-⊗

        map-f₀ {𝔍} {Δ} {Γ} {α} (app {𝔍₀} {𝔍₁} {𝔧 = 𝔧} t s) =
          let t' = map-f₀ t
              s' = map-f₀ s
          in {!!}
            -- ⟦ Γ ↷ (𝔍₀ ⋆ 𝔍₁) ⋆ Δ ⟧                 ⟶⟨ {!!} ⟩
            -- ⟦ Γ ↷ (𝔍₀ ⋆ 𝔍₁) ⟧ ⊗ ⟦ Γ ↷ Δ ⟧        ⟶⟨ {!!} ⟩
            -- ⟦ (Γ ↷ 𝔍₀) ⋆ (Γ ↷ 𝔍₁) ⟧ ⊗ ⟦ Γ ↷ Δ ⟧        ⟶⟨ {!!} ⟩
            -- ⟦ Γ ↷ 𝔍₀ ⟧ ⊗ ⟦ Γ ↷ 𝔍₁ ⟧ ⊗ ⟦ Γ ↷ Δ ⟧        ⟶⟨ {!!} ⟩
            -- ⟦ Γ ↷ 𝔍₀ ⟧ ⊗ (⟦ Γ ↷ 𝔍₁ ⟧ ⊗ ◌) ⊗ ⟦ Γ ↷ Δ ⟧        ⟶⟨ map-⊗ (map-⊗ id {!!}) id  ⟩
            -- ⟦ Γ ↷ 𝔍₀ ⟧ ⊗ (⟦ Γ ↷ 𝔍₁ ⟧ ⊗ ⟦ Γ ↷ [] ⟧) ⊗ ⟦ Γ ↷ Δ ⟧ ⟶⟨ map-⊗ (map-⊗ id s') id  ⟩
            -- ⟦ Γ ↷ 𝔍₀ ⟧ ⊗ (⟦ Γ ↷ 𝔧 ⟧                ) ⊗ ⟦ Γ ↷ Δ ⟧        ⟶⟨ assoc-l-⊗ ⟩
            -- ⟦ Γ ↷ 𝔍₀ ⟧ ⊗ (⟦ Γ ↷ 𝔧 ⟧ ⊗ ⟦ Γ ↷ Δ ⟧)        ⟶⟨ id ⟩
            -- ⟦ Γ ↷ 𝔍₀ ⟧ ⊗ (⟦ (Γ ↷ 𝔧) ∷ (Γ ↷ Δ) ⟧)        ⟶⟨ {!!} ⟩
            -- ⟦ Γ ↷ 𝔍₀ ⟧ ⊗ ⟦ Γ ↷ (𝔧 ∷ Δ) ⟧          ⟶⟨ t' ⟩
            -- ⟦ Γ ↷ α ⟧                               ⟶id

        map-f₀ (con {Γ} {Δ} {α} x) =
          let x' = ⟨ ϕ ⟩ x
          in ⟦ Γ ↷ Δ ⟧   ⟶⟨ ⟨ ⟦↷-ListJdg⟧ {Δ = Δ} ⟩ ⟩
            Γ ↷ ⟦ Δ ⟧   ⟶⟨ map x' ⟩
            Γ ↷ ⟦ α ⟧    ⟶⟨ ⟨ ⟦↷-Jdg⟧ ⁻¹ ⟩ ⟩
            ⟦ Γ ↷ α ⟧    ⟶id

        map-f₀ {𝔍} {Δ} {Γ} {α} (lam {𝔍₀} {𝔍₁} {α = α'} {αs = αs'} {β} v x) =
          let x' = map-f₀ x
              v' = map-f₀ v
          in {!!}
            -- ⟦ Γ ↷ (𝔍₀ ⋆ 𝔍₁) ⋆ Δ ⟧                 ⟶⟨ ? ⟩
            -- ⟦ Γ ↷ (𝔍₀ ⋆ 𝔍₁) ⟧ ⊗ ⟦ Γ ↷ Δ ⟧        ⟶⟨ {!!} ⟩
            -- ⟦ (Γ ↷ 𝔍₀) ⋆ (Γ ↷ 𝔍₁) ⟧ ⊗ ⟦ Γ ↷ Δ ⟧        ⟶⟨ {!!} ⟩
            -- ⟦ Γ ↷ 𝔍₀ ⟧ ⊗ ⟦ Γ ↷ 𝔍₁ ⟧ ⊗ ⟦ Γ ↷ Δ ⟧        ⟶⟨ {!!} ⟩
            -- ⟦ Γ ↷ 𝔍₀ ⟧ ⊗ ⟦ (Γ ↷ 𝔍₁) ⋆ (Γ ↷ Δ) ⟧        ⟶⟨ {!!} ⟩
            -- ⟦ Γ ↷ 𝔍₀ ⟧ ⊗ ⟦ Γ ↷ (𝔍₁ ⋆ Δ) ⟧               ⟶⟨ {!!} ⟩
            -- (⟦ Γ ↷ 𝔍₀ ⟧ ⊗ ◌) ⊗ ⟦ Γ ↷ (𝔍₁ ⋆ Δ) ⟧         ⟶⟨ id ⟩
            -- (⟦ Γ ↷ 𝔍₀ ⟧ ⊗ ⟦ Γ ↷ [] ⟧) ⊗ ⟦ Γ ↷ (𝔍₁ ⋆ Δ) ⟧  ⟶⟨ {!!} ⟩
            -- ⟦(Γ ↷ ([] ⊢ ∂ₖ α'))⟧ ⊗ ⟦ Γ ↷ (𝔍₁ ⋆ Δ) ⟧         ⟶⟨ {!!} ⟩
            -- ⟦(Γ ⊢ ∂ₖ α')⟧         ⊗ (Γ ↷ ⟦ (𝔍₁ ⋆ Δ) ⟧)       ⟶⟨ varSkip ⟩
            -- (Γ ⋆ ⦋ α' ⦌) ↷ ⟦ 𝔍₁ ⋆ Δ ⟧                        ⟶⟨ {!!} ⟩
            -- ⟦ (Γ ⋆ ⦋ α' ⦌) ↷ (𝔍₁ ⋆ Δ) ⟧                        ⟶⟨ {!!} ⟩
            -- ⟦ ((Γ ⋆ ⦋ α' ⦌) ↷ 𝔍₁) ⋆ ((Γ ⋆ ⦋ α' ⦌) ↷ Δ) ⟧      ⟶⟨ {!!} ⟩
            -- ⟦ ((Γ ⋆ ⦋ α' ⦌) ↷ 𝔍₁) ⟧ ⊗ ⟦ ((Γ ⋆ ⦋ α' ⦌) ↷ Δ) ⟧  ⟶⟨ x' ⟩
            -- ⟦ ((Γ ⋆ ⦋ α' ⦌) ↷ (αs' ⊢ β)) ⟧                     ⟶⟨ {!!} ⟩
            -- -- ⟦ ((Γ ⋆ ⦋ α' ⦌) ↷ (αs' ↷ ⊦ β)) ⟧                     ⟶⟨ {!!} ⟩
            -- -- ⟦ (((Γ ⋆ ⦋ α' ⦌) ⋆ αs') ↷ ⊦ β) ⟧                     ⟶⟨ {!!} ⟩
            -- ⟦ Γ ↷ ((α' ∷ αs') ⊢ β) ⟧   ⟶id
        map-f₀ (var {Γ} {α} x) =
          let x' = varProj x
          in ⟦ Γ ↷ [] ⟧                  ⟶⟨ x' ⟩
             ⟦ Γ ⊢ α ⟧                    ⟶⟨ {!!} ⟩
             ⟦ Γ ↷ ([] ⊢ α) ⟧            ⟶id


      map-f : ∀{a b} ->
              Subs (MTCDefinitions._⊩ᶠ'_ γ) ⟨ a ⟩ ⟨ b ⟩
              -> Hom (f a) (f b)
      map-f {incl .⦋⦌} {incl .⦋⦌} [] = id
      map-f {incl .(Γ ⋆ Γ')} {incl .(_ ∷ _)} (_∷_ {Γ} {Γ'} x s) = {!!}

      isFunctor:f : isFunctor ′ ⟨ F γ ⟩ ′ ′ ⟨ ℳ ⟩ ′ f
      isFunctor.map isFunctor:f = map-f
      isFunctor.isSetoidHom:map isFunctor:f = {!!}
      isFunctor.functoriality-id isFunctor:f = {!!}
      isFunctor.functoriality-◆ isFunctor:f = {!!}

module _ {K : Kinding 𝑖₁} where
  instance
    isLogicalFramework:MTC : isLogicalFramework (CwJ K (_ , _ , _)) (MTC K _) -- (MTC (𝑙 , (𝑖 ⊔ 𝑙)))
    isLogicalFramework.LFTerm (isLogicalFramework:MTC) = F
    isLogicalFramework.LFSig isLogicalFramework:MTC = U
    isLogicalFramework.isFunctor:LFTerm isLogicalFramework:MTC = {!!}
    isLogicalFramework.isFunctor:LFSig isLogicalFramework:MTC = {!!}
    isLogicalFramework.interp isLogicalFramework:MTC {γ} {ℳ} = i {γ = γ} {ℳ = ℳ}

    -- where
    --   f : ⟨ F γ ⟩ -> ⟨ ℳ ⟩
    --   f (incl x) = rec-Ctx-⦿ JObj x -- (λ 𝔧 -> JObj (map-Jdg-⦿ ⟨ ϕ ⟩ 𝔧)) x
    {-

      open MTCDefinitions γ

      mutual
        -- map-f₀-var : ∀{a b} ->
        --         (_⊩ᶠ↓_)
        --         -- (map-Ctx-⦿ (λ 𝔧 -> map-Jdg-⦿ kind 𝔧 ◀ main) ⟨ a ⟩)
        --         (map-Ctx-⦿ (map-Jdg-⦿ kind) ⟨ a ⟩)
        --         ((map-Jdg-⦿ kind) b ◀ var) →
        --         Hom (f a) (f (incl ([] ,, b)))

        map-f₀-var : ∀{a b τ α Τ} ->
                (_⊩ᶠ↓_)
                (map-Ctx-⦿ (map-Jdg-⦿ kind) ⟨ a ⟩)
                ((map-Ctx-⦿ kind) b ⊢ α ◀ var) →
                (⟦ Τ ⊩ τ ⟧-R ≣ α) ->
                Hom (f a) (f (incl ([] ,, b ↷ τ)))

        map-f₀-var {a} {[]} (getapp ())
        map-f₀-var {a} {(G ,, x)} (MTCDefinitions.getapp ())
        map-f₀-var {a} {(G ,, x)} {[] ⊢ τ} {α} {Τ} (suc te te2) p =
          let y1 = map-f₀ {τ = [] ⊢ ∂ₖ x} te refl-≣
              y2 = map-f₀-var {τ = [] ⊢ τ} {Τ = Τ} te2 p
          in diag ◆ (map-⊗ (y1 ◆ unit-l-⊗) (y2 ◆ unit-l-⊗) ◆ varSkip ◆ unit-l-⊗-⁻¹)
        map-f₀-var {a} {(G ,, x)} {τ ⊢ τ'} {α} {Τ} (suc te te2) p = {!!}
        map-f₀-var {a} {(G ,, x)} {τ} {α} {Τ} (zero te) p with arrify-R-kind {Γ = Τ} {τ = τ} p
        ... | refl-≣ , refl-≣ =
          let y1 = map-f₀ {τ = [] ⊢ ∂ₖ x} te refl-≣
          in y1 ◆ map-⊗ id (varTake {Γ = G} {a = x})


        map-f₀-app : ∀{a b τ α Τ} ->
                (_⊩ᶠ↓-app_)
                (map-Ctx-⦿ (map-Jdg-⦿ kind) ⟨ a ⟩)
                -- (map-Ctx-⦿ (λ 𝔧 -> map-Jdg-⦿ kind 𝔧 ◀ main) ⟨ a ⟩)
                ((map-Ctx-⦿ kind) b ⊢ α ◀ main) →
                (⟦ Τ ⊩ τ ⟧-R ≣ α) ->
                Hom (f a) (f (incl ([] ,, b ↷ τ)))
        map-f₀-app {a} {b} {G ⊢ t} {α} {Τ} (MTCDefinitions.app {_} {α₁} {𝔧} q x y) p =
          let t1 = map-f₀-app {_} {_} {(G) ⊢ t} {_} {Τ = ([] ,, 𝔧) ⋆ Τ} x {!!}
              t2 = map-f₀ {_} {_} {𝔧} y q
              -- t2 = map-f₀ {_} {_} {[] ⊢ α₁} y refl-≣
          in {!!}
        map-f₀-app {a} {b} {τ} {α} {Τ} (var x) p = map-f₀-var {a} {b} {τ} {α} {Τ} x p
        map-f₀-app {a} {b} (con {_} {ts ⊩ t} x x₁) p = {!!}
        map-f₀-app {a} {b} (meta x) p = {!!}

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
        ... | (refl-≣ , refl-≣) = map-f₀-app {Τ = []} x p


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

      isFunctor:f : isFunctor ′ ⟨ F γ ⟩ ′ ′ ⟨ ℳ ⟩ ′ f
      isFunctor.map isFunctor:f = map-f
      isFunctor.isSetoidHom:map isFunctor:f = {!!}
      isFunctor.functoriality-id isFunctor:f = {!!}
      isFunctor.functoriality-◆ isFunctor:f = {!!}
      -}



{-
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
-}
