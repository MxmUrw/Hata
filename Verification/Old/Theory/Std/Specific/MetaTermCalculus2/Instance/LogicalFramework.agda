
module Verification.Core.Theory.Std.Specific.MetaTermCalculus2.Instance.LogicalFramework where

open import Verification.Core.Conventions hiding (Structure ; _◀)
open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Category.Std.Functor.Definition
open import Verification.Core.Data.Universe.Definition
open import Verification.Core.Data.Universe.Instance.Category
open import Verification.Core.Algebra.Monoid.Definition
open import Verification.Core.Algebra.Monoid.Free
open import Verification.Core.Algebra.MonoidAction.Definition
open import Verification.Core.Order.Lattice
open import Verification.Core.Category.Std.Category.Structured.Monoidal.Definition
open import Verification.Core.Category.Std.Morphism.Iso
open import Verification.Core.Theory.Std.Specific.MetaTermCalculus2.Definition
open import Verification.Core.Theory.Std.Generic.TypeTheory.Simple
open import Verification.Core.Theory.Std.Generic.TypeTheory.Simple.Judgement2
open import Verification.Core.Theory.Std.Generic.TypeTheory.Definition
open import Verification.Core.Theory.Std.Generic.LogicalFramework.Definition
open import Verification.Core.Theory.Std.TypologicalTypeTheory.CwJ.Definition


module _ {𝒞 : 𝒰 𝑖} {{_ : isCategory {𝑗} 𝒞}} where
  infixr 10 _⟶⟨_⟩_
  _⟶⟨_⟩_ : ∀(a : 𝒞) {b c : 𝒞} -> (ϕ : a ⟶ b) -> (ψ : b ⟶ c ) -> a ⟶ c
  _⟶⟨_⟩_ _ ϕ ψ = ϕ ◆ ψ

  _⟶id : ∀(a : 𝒞) -> a ⟶ a
  _⟶id a = id


pattern make∑i' a b = make∑i {a} {{b}}
pattern since' a b c = ′ a ′ {b} {{c}}

private
  module _ {K : Kinding 𝑖₁} where
    U : CwJ K (𝑘 , 𝑖₂ , 𝑗) -> MetaTermCalculus K _
    U 𝒞 = record {TermCon = JHom}



    F : ∀{𝑖} -> MetaTermCalculus K 𝑖 -> CwJ K _
    F γ = MTCCat γ since (isCwJ:MTCCat {γ = γ})
      where open MTCDefinitions γ


  -- module MTC-λ₋ {𝑖 : 𝔏} {K : Kinding 𝑖} {γ : MetaTermCalculus K 𝑖}
  --        {ℳ : CwJ K (𝑖 , _ , 𝑖)}
  --        (ϕ : Hom γ (U ℳ)) where

module MTC-λ₋ {𝑖 : 𝔏} {K : Kinding 𝑖} {γ : MetaTermCalculus K 𝑘}
        {ℳ : 𝒰 𝑗₂}
        {{oCategory : isCategory {𝑗₁} ℳ}}
        {{oMonoidal : isMonoidal ′ ℳ ′}}
        {{pℳ       : isCwJ K ′ ℳ ′}}
        -- {ℳ : CwJ K 𝑗}
        (ϕ : Hom-MTC γ (U ′ ℳ ′)) where


    private

  -- i : ∀{K : Kinding 𝑖} {γ : MetaTermCalculus K (𝑖)} -> ∀ {ℳ} -> (Hom γ (U ℳ)) -> (Hom (F γ) ℳ)
  -- i {γ = γ} {since' ℳ (oℳ) pℳ} ϕ = f since isFunctor:f -- 18 sek instance search w/o spec | 14 with spec
  -- i {γ = γ} {since' ℳ (make∑i {make∑i {oCat}}) pℳ} ϕ = f since isFunctor:f

      -- pℳ = of ℳ
      -- oℳ = _:&_.oldProof ℳ
      -- oMonoidal = ∑i_.isnd oℳ
      -- oCategory = ∑i_.isnd (∑i_.ifst oℳ)
      oMonoid = isMonoidal.isMonoid:this oMonoidal

      instance
        _ : isSetoid ℳ
        _ = isSetoid:byCategory

      open MTCDefinitions γ

      f : ⟨ F γ ⟩ -> ℳ
      f (incl x) = ⟦ x ⟧

      id' : ∀{a : ℳ} -> a ⟶ a
      id' = id -- {{oCategory}}
      -- {{∑i_.isnd (∑i_.ifst oℳ)}}

      infixr 10 _⟶'⟨_⟩_
      _⟶'⟨_⟩_ : ∀(a : ℳ) {b c : ℳ} -> (ϕ : a ⟶ b) -> (ψ : b ⟶ c ) -> a ⟶ c
      _⟶'⟨_⟩_ a ϕ ψ = _◆_ ϕ ψ
      -- _⟶'⟨_⟩_ a ϕ ψ = _◆_ {{oCategory}} ϕ ψ

      _⟶id' : ∀(a : ℳ) -> a ⟶ a
      _⟶id' a = id -- {{oCategory}}
      -- _⟶id' a = id {{oCategory}}

      _⋆'_ : ∀{A : 𝒰 ℓ} -> List A -> List A -> List A
      _⋆'_ = _++-List_

      -- {{∑i_.isnd (∑i_.ifst oℳ)}} ϕ ψ

      infixl 70 _⊗'_ _⇃⊗⇂'_
      _⇃⊗⇂'_ : ∀{a b c d : ℳ} -> (f : a ⟶ b) (g : c ⟶ d) -> (a ⋆ c ⟶ b ⋆ d)
      _⇃⊗⇂'_ = λ₊ (map)

      _⊗'_ : ℳ  -> ℳ  -> ℳ 
      _⊗'_ = _⋆_ -- {{isMonoidal.isMonoid:this oMonoidal}}


      mutual

        map-f₀ : ∀{𝔍 Δ Γ α} ->
                𝔍 ⊩ᶠ (Γ ∣ Δ ⇒ α)
                -> Hom (⟦ Γ ⟧-LK ⊗' ⟦ (𝔍 ⋆' Δ) ⟧-LCJ) (⟦ Γ ⟧-LK ⊗' ⟦ α ⟧-CJ)
        map-f₀ (meta {αs} {α}) = (id' ⇃⊗⇂' ⟨ unit-r-⋆ ⟩)

        map-f₀ {𝔍} {Δ} {Γ} {α} (app {𝔍₀} {𝔍₁} {𝔧 = 𝔧} t s) =
          let t' = map-f₀ t
              s' = map-f₀ s
          in  {-  ⟦ Γ ⟧-LK ⊗' ⟦ (𝔍₁ ⋆' 𝔍₀) ⋆' Δ ⟧-LCJ                 -} _ ⟶'⟨ map (id' , ⟨ ≀⟦⟧≀ (assoc-l-⋆ {a = 𝔍₁} {𝔍₀} {Δ}) ⟩) ⟩
              {-  ⟦ Γ ⟧-LK ⊗' ⟦ 𝔍₁ ⋆' (𝔍₀ ⋆' Δ) ⟧-LCJ                 -} _ ⟶'⟨ id' ⇃⊗⇂' ⟨ ⟦⊗⟧ {Γ = 𝔍₁} {Δ = 𝔍₀ ⋆' Δ} ⟩ ⟩
              {-  ⟦ Γ ⟧-LK ⊗' (⟦ 𝔍₁ ⟧-LCJ ⊗' ⟦ 𝔍₀ ⋆' Δ ⟧-LCJ)         -} _ ⟶'⟨ ⟨ assoc-l-⋆ {{oMonoid}} ⁻¹ ⟩ ⟩
              {-  ⟦ Γ ⟧-LK ⊗' ⟦ 𝔍₁ ⟧-LCJ ⊗' ⟦ 𝔍₀ ⋆' Δ ⟧-LCJ           -} _ ⟶'⟨ id' ⇃⊗⇂' ⟨ ≀⟦⟧≀ (unit-r-⋆ {a = 𝔍₁} ⁻¹) ⟩ ⇃⊗⇂' id' ⟩
              {-  ⟦ Γ ⟧-LK ⊗' ⟦ 𝔍₁ ⋆' [] ⟧-LCJ ⊗' ⟦ 𝔍₀ ⋆' Δ ⟧-LCJ     -} _ ⟶'⟨ s' ⇃⊗⇂' id' ⟩
              {-  ⟦ Γ ⟧-LK ⊗' ⟦ 𝔧 ⟧-CJ ⊗' ⟦ 𝔍₀ ⋆' Δ ⟧-LCJ             -} _  ⟶'⟨ id' ⇃⊗⇂' ⟨ ⟦⊗⟧ {Γ = 𝔍₀} {Δ = Δ} ⟩ ⟩
              {-  ⟦ Γ ⟧-LK ⊗' ⟦ 𝔧 ⟧-CJ ⊗' (⟦ 𝔍₀ ⟧-LCJ ⊗' ⟦ Δ ⟧-LCJ)   -} _  ⟶'⟨ ⟨ assoc-l-⋆ {{oMonoid}} ⟩ ⟩
              {-  ⟦ Γ ⟧-LK ⊗' (⟦ 𝔧 ⟧-CJ ⊗' (⟦ 𝔍₀ ⟧-LCJ ⊗' ⟦ Δ ⟧-LCJ)) -} _  ⟶'⟨ id' ⇃⊗⇂' ⟨ assoc-l-⋆ {{oMonoid}} ⁻¹ ⟩ ⟩
              {-  ⟦ Γ ⟧-LK ⊗' ((⟦ 𝔧 ⟧-CJ ⊗' ⟦ 𝔍₀ ⟧-LCJ) ⊗' ⟦ Δ ⟧-LCJ) -} _  ⟶'⟨ id' ⇃⊗⇂' (braid {{pℳ}} ⇃⊗⇂' id') ⟩
              {-  ⟦ Γ ⟧-LK ⊗' ((⟦ 𝔍₀ ⟧-LCJ ⊗' ⟦ 𝔧 ⟧-CJ) ⊗' ⟦ Δ ⟧-LCJ) -} _  ⟶'⟨ id' ⇃⊗⇂' ⟨ assoc-l-⋆ {{oMonoid}} ⟩ ⟩
              {-  ⟦ Γ ⟧-LK ⊗' (⟦ 𝔍₀ ⟧-LCJ ⊗' (⟦ 𝔧 ⟧-CJ ⊗' ⟦ Δ ⟧-LCJ)) -} _  ⟶'⟨ id' ⇃⊗⇂' (id' ⇃⊗⇂' (⟨ unit-r-⋆ {{oMonoid}} ⁻¹ ⟩ ⇃⊗⇂' id') ) ⟩
              {-  ⟦ Γ ⟧-LK ⊗' (⟦ 𝔍₀ ⟧-LCJ ⊗' (⟦ 𝔧 ∷ [] ⟧-LCJ ⊗' ⟦ Δ ⟧-LCJ)) -} _  ⟶'⟨ id' ⇃⊗⇂' (id' ⇃⊗⇂' ⟨ ⟦⊗⟧ {Γ = 𝔧 ∷ []} {Δ = Δ} ⁻¹ ⟩ ) ⟩
              {-  ⟦ Γ ⟧-LK ⊗' (⟦ 𝔍₀ ⟧-LCJ ⊗' (⟦ 𝔧 ∷ Δ ⟧-LCJ))          -} _ ⟶'⟨ id' ⇃⊗⇂' ⟨ ⟦⊗⟧ {Γ = 𝔍₀} {Δ = 𝔧 ∷ Δ} ⁻¹ ⟩ ⟩
              {-  ⟦ Γ ⟧-LK ⊗' (⟦ 𝔍₀ ⋆' (𝔧 ∷ Δ) ⟧-LCJ)                 -} _  ⟶'⟨ t' ⟩
                ⟦ Γ ⟧-LK ⊗' ⟦ α ⟧-CJ                                  ⟶id


        map-f₀ (con {Γ} {Δ} {α} x) =
          let x' = ⟨ ϕ ⟩ x
          in id' ⇃⊗⇂' x'

        map-f₀ {𝔍} {Δ} {Γ} {α} (lam {𝔍₀} {𝔍₁} {α = α'} {αs = αs'} {β} v x) =
          let x' = map-f₀ x
              v' = map-f₀ v
              P  = ⟦ Γ ⟧-LK ⊗' ⟦ (𝔍₀ ⋆' 𝔍₁) ⋆' Δ ⟧-LCJ                ⟶'⟨ map (id' , ⟨ ≀⟦⟧≀ (assoc-l-⋆ {a = 𝔍₀} {𝔍₁} {Δ}) ⟩) ⟩
                 {-  ⟦ Γ ⟧-LK ⊗' ⟦ 𝔍₀ ⋆' (𝔍₁ ⋆' Δ) ⟧-LCJ               -} _ ⟶'⟨ id' ⇃⊗⇂' ⟨ ⟦⊗⟧ {Γ = 𝔍₀} {Δ = 𝔍₁ ⋆' Δ} ⟩ ⟩
                 {-  ⟦ Γ ⟧-LK ⊗' (⟦ 𝔍₀ ⟧-LCJ ⊗' ⟦ 𝔍₁ ⋆' Δ ⟧-LCJ)       -} _ ⟶'⟨ ⟨ assoc-l-⋆ {{oMonoid}} ⁻¹ ⟩ ⟩
                 {-  ⟦ Γ ⟧-LK ⊗' ⟦ 𝔍₀ ⟧-LCJ ⊗' ⟦ 𝔍₁ ⋆' Δ ⟧-LCJ         -} _ ⟶'⟨ id' ⇃⊗⇂' ⟨ ≀⟦⟧≀ (unit-r-⋆ {a = 𝔍₀} ⁻¹) ⟩ ⇃⊗⇂' id' ⟩
                 {-  ⟦ Γ ⟧-LK ⊗' ⟦ 𝔍₀ ⋆' [] ⟧-LCJ ⊗' ⟦ 𝔍₁ ⋆' Δ ⟧-LCJ   -} _ ⟶'⟨ v' ⇃⊗⇂' id' ⟩
                 {-  ⟦ Γ ⟧-LK ⊗' ⟦ [] ⊢ ∂ₖ α' ⟧-CJ ⊗' ⟦ 𝔍₁ ⋆' Δ ⟧-LCJ  -} _ ⟶'⟨ id' ⇃⊗⇂' ⟨ unit-l-⋆ {{oMonoid}} ⟩ ⇃⊗⇂' id' ⟩
                 {-  ⟦ Γ ⟧-LK ⊗' ⊦ (∂ₖ α') ⊗' ⟦ 𝔍₁ ⋆' Δ ⟧-LCJ          -} _ ⟶'⟨ varTake {{pℳ}} {Γ = Γ} ⇃⊗⇂' id' ⟩
                 {-  ⟦ α' ∷ Γ ⟧-LK ⊗' ⟦ 𝔍₁ ⋆' Δ ⟧-LCJ                  -} _ ⟶'⟨ x' ⟩
                 {-  ⟦ α' ∷ Γ ⟧-LK ⊗' ⟦ αs' ⊢ β ⟧-CJ                   -} _  ⟶'⟨ braid {{pℳ}} ⇃⊗⇂' id' ⟩
                 {-  ⟦ Γ ⟧-LK ⊗' ⊦ α' ⊗' ⟦ αs' ⊢ β ⟧-CJ                -} _ ⟶'⟨ ⟨ assoc-l-⋆ {{oMonoid}} ⟩ ⟩
                 {-  ⟦ Γ ⟧-LK ⊗' (⊦ α' ⊗' ⟦ αs' ⊢ β ⟧-CJ)              -} _ ⟶'⟨ id' ⇃⊗⇂' ⟨ assoc-l-⋆ {{oMonoid}} ⁻¹ ⟩ ⟩
                   ⟦ Γ ⟧-LK ⊗' ⟦ (α' ∷ αs') ⊢ β ⟧-CJ                  ⟶id'
          in P

        map-f₀ (var {Γ} {α} x) =
          let x' = varProj x
          in ⟦ Γ ⟧-LK ⊗' ◌               ⟶'⟨ ⟨ unit-r-⋆ {{oMonoid}} ⟩ ⟩
             {- ⟦ Γ ⟧-LK      -} _              ⟶'⟨ x' ⟩
             {- ⟦ Γ ⊢ α ⟧-CJ  -} _                ⟶'⟨ id' ⇃⊗⇂' ⟨ unit-l-⋆ {{oMonoid}} ⁻¹ ⟩ ⟩
             ⟦ Γ ⟧-LK ⊗' ⟦ [] ⊢ α ⟧-CJ      ⟶id'

      map-f : ∀{a b} ->
              Subs (MTCDefinitions._⊩ᶠ'_ γ) ⟨ a ⟩ ⟨ b ⟩
              -> Hom (f a) (f b)
      map-f {incl .⦋⦌} {incl .⦋⦌} [] = id'
      map-f {incl .(Γ ⋆ Γ')} {incl (k ∷ Δ)} (_∷_ {Γ} {Γ'} x s) =
        let x' = map-f₀ x
            s' = map-f s
        in ⟦ Γ ⋆ Γ' ⟧-LCJ               ⟶'⟨ ⟨ ⟦⊗⟧ {Γ = Γ} {Δ = Γ'} ⟩ ⟩
           {- ⟦ Γ ⟧-LCJ ⊗' ⟦ Γ' ⟧-LCJ       -} _     ⟶'⟨ ⟨ unit-l-⋆ {{oMonoid}} ⁻¹ ⟩ ⇃⊗⇂' s' ⟩
           {- ◌ ⊗' ⟦ Γ ⟧-LCJ ⊗' ⟦ Δ ⟧-LCJ   -} _     ⟶'⟨ id' ⇃⊗⇂' ⟨(≀⟦⟧≀ {Γ = Γ} {Γ' = Γ ⋆ ⦋⦌} (unit-r-⋆ ⁻¹))⟩ ⇃⊗⇂' id' ⟩
           {- ◌ ⊗' ⟦ Γ ⋆ ⦋⦌ ⟧ ⊗' ⟦ Δ ⟧-LCJ  -} _ ⟶'⟨ (x' ◆ ⟨ unit-l-⋆ {{oMonoid}} ⟩) ⇃⊗⇂' id' ⟩
           ⟦ k ⟧-CJ ⊗' ⟦ Δ ⟧-LCJ           ⟶id'

      isFunctor:f : isFunctor ′ ⟨ F γ ⟩ ′ ′ ℳ ′ f
      isFunctor.map isFunctor:f = map-f
      isFunctor.isSetoidHom:map isFunctor:f = {!!}
      isFunctor.functoriality-id isFunctor:f = {!!}
      isFunctor.functoriality-◆ isFunctor:f = {!!}

    Proof : Functor ′ ⟨ (F γ) ⟩ ′ ′ ℳ ′
    Proof = f since isFunctor:f

module MTC-λ₋2 {𝑖 : 𝔏} {K : Kinding 𝑖} {γ : MetaTermCalculus K 𝑘}
        (ℳ : CwJ K 𝑗)
        (ϕ : Hom-MTC γ (U ℳ)) where
  Proof = MTC-λ₋.Proof {γ = γ} {ℳ = ⟨ ℳ ⟩} ϕ

module _ {K : Kinding 𝑖₁} where
  instance
    isLogicalFramework:MTC : isLogicalFramework (CwJ K (_ , _ , _)) (MTC K 𝑖₁) -- (MTC (𝑙 , (𝑖 ⊔ 𝑙)))
    isLogicalFramework.LFTerm (isLogicalFramework:MTC) = F
    isLogicalFramework.LFSig isLogicalFramework:MTC = U
    isLogicalFramework.isFunctor:LFTerm isLogicalFramework:MTC = {!!}
    isLogicalFramework.isFunctor:LFSig isLogicalFramework:MTC = {!!}
    isLogicalFramework.interp isLogicalFramework:MTC {γ} {ℳ} = MTC-λ₋.Proof {γ = γ} {ℳ = ⟨ ℳ ⟩}

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
