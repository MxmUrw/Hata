
module Verification.Experimental.Category.Std.Fibration.Definition where

open import Verification.Experimental.Conventions
open import Verification.Experimental.Meta.Structure
open import Verification.Experimental.Set.Setoid.Definition
open import Verification.Experimental.Set.Set.Definition
open import Verification.Experimental.Set.Set.Instance.Category
open import Verification.Experimental.Category.Std.Category.Definition
open import Verification.Experimental.Category.Std.Functor.Definition
open import Verification.Experimental.Category.Std.Category.Opposite
open import Verification.Experimental.Category.Std.Category.Instance.Category
open import Verification.Experimental.Category.Std.Limit.Specific.Pullback

open import Verification.Experimental.Data.Universe.Definition
open import Verification.Experimental.Data.Universe.Everything

--
-- The definition of (Grothendieck) fibrations
-- (following the definition at https://ncatlab.org/nlab/show/Grothendieck+fibration)
--


-- private variable
  -- ℬ : Category 𝑖
  -- ℰ : Category 𝑗
  -- e e₀ e₁ e₂ : ⟨ ℰ ⟩


-- module _  where
-- record FullSubsetoid (X : Setoid 𝑖) (ϕ : ⟨ X ⟩ -> 𝒰 𝑗) : 𝒰 𝑖 where
--   field 


isSetoid:FullSubsetoid : (X : Setoid 𝑖) {A : 𝒰 𝑗} (ϕ : A -> ⟨ X ⟩) -> isSetoid _ A
isSetoid._∼'_ (isSetoid:FullSubsetoid X ϕ) = λ a b -> ϕ a ∼ ϕ b
isSetoid.isEquivRel:∼ (isSetoid:FullSubsetoid X ϕ) = equivRel (incl refl) (λ p -> incl (sym ⟨ p ⟩)) (λ p q -> incl (⟨ p ⟩ ∙ ⟨ q ⟩))

isContr-Std : (A : 𝒰 _) {{_ : Setoid 𝑖 on A}} -> 𝒰 _
isContr-Std A = ∑ λ (a : A) -> ∀ (b : A) -> a ∼ b
-- ∀ (a b : A) -> a ∼ b


module _ (ℰ : Category 𝑗) (ℬ : Category 𝑖) where
  module _ (p : Functor ℰ ℬ) where

    module _ {e₀ e₁ e₂} (ϕ : e₁ ⟶ e₀) (ψ : e₂ ⟶ e₀) (g : ⟨ p ⟩ e₂ ⟶ ⟨ p ⟩ e₁) (p : g ◆ map ϕ ∼ map ψ) where

      record isCartesianLift (χ : e₂ ⟶ e₁) : 𝒰 (𝑗 ､ 𝑖) where
        field cartesianLiftFills : (χ ◆ ϕ) ∼ ψ
        field cartesianLiftSection : map χ ∼ g

      CartesianLift = _ :& isCartesianLift

    module _ {e₀ e₁ e₂} {ϕ : e₁ ⟶ e₀} {ψ : e₂ ⟶ e₀} {g : ⟨ p ⟩ e₂ ⟶ ⟨ p ⟩ e₁} {p : g ◆ map ϕ ∼ map ψ} where
      instance
        isSetoid:CartesianLift : isSetoid _ (CartesianLift ϕ ψ g p)
        isSetoid:CartesianLift = isSetoid:FullSubsetoid ′(e₂ ⟶ e₁)′ ⟨_⟩

    record isCartesian {e₁ e₀ : ⟨ ℰ ⟩} (ϕ : e₁ ⟶ e₀) : 𝒰 (𝑗 ､ 𝑖) where
      field uniqueCartesianLift : ∀{e₂} (ψ : e₂ ⟶ e₀) (g : ⟨ p ⟩ e₂ ⟶ ⟨ p ⟩ e₁) (p : g ◆ map ϕ ∼ map ψ) -> isContr-Std (CartesianLift ϕ ψ g p)

    Cartesian : ∀(e₁ e₀ : ⟨ ℰ ⟩) -> 𝒰 _
    Cartesian e₁ e₀ = (e₁ ⟶ e₀) :& isCartesian

  record isFibrationalLift (p : Functor ℰ ℬ) {e b} (f : b ⟶ ⟨ p ⟩ e) {e'} (ϕ : Cartesian p e' e) : 𝒰 𝑖 where
    field fibrationalLiftObjectSection : ⟨ p ⟩ e' ≡ b
    field fibrationalLiftHomSection : transport (λ i -> fibrationalLiftObjectSection i ⟶ ⟨ p ⟩ e) (map ⟨ ϕ ⟩) ∼ f

  record isFibration (p : Functor ℰ ℬ) : 𝒰 (𝑖 ､ 𝑗) where
    field liftCartesian : ∀{e : ⟨ ℰ ⟩} {b : ⟨ ℬ ⟩} (f : b ⟶ ⟨ p ⟩ e) -> ∑ λ e' -> ∑ λ (ϕ : Cartesian p e' e) -> isFibrationalLift p f ϕ

  Fibration = _ :& isFibration


module _ {ℰ : Category 𝑗} {ℬ : Category 𝑖} where

  module _ (p : Fibration ℰ ℬ) (b : ⟨ ℬ ⟩) where
    record isFiber (e : Obj ℰ) : 𝒰 (𝑗 ､ 𝑖) where
      field isSectionFiber : ⟨ p ⟩ ⟨ e ⟩ ≡ b

    open isFiber public

    Fiber = _ :& isFiber

  module _ {p : Fibration ℰ ℬ} {b : ⟨ ℬ ⟩} where

    private
      p' : Functor ℰ ℬ
      p' = ′ ⟨ p ⟩ ′

    instance
      isCategory:Fiber : isCategory _ (Fiber p b)
      -- isCategory.Hom' isCategory:Fiber = λ e₀ e₁ -> ∑ λ (ϕ : ⟨ e₀ ⟩ ⟶ ⟨ e₁ ⟩) -> 𝟙-𝒰
      isCategory.Hom' isCategory:Fiber = λ e₀ e₁ -> ∑ λ (ϕ : ⟨ e₀ ⟩ ⟶ ⟨ e₁ ⟩) -> transport (λ i -> isSectionFiber (of e₀) i ⟶ isSectionFiber (of e₁) i) (map {{of p'}} ϕ) ∼ id
      isCategory.isSetoid:Hom isCategory:Fiber = {!!}
      -- λ {e₀} {e₁} -> isSetoid:FullSubsetoid (′ ⟨ e₀ ⟩ ⟶ ⟨ e₁ ⟩ ′) fst
      isCategory.id isCategory:Fiber = {!!}
      isCategory._◆_ isCategory:Fiber = {!!}
      isCategory.unit-l-◆ isCategory:Fiber = {!!}
      isCategory.unit-r-◆ isCategory:Fiber = {!!}
      isCategory.unit-2-◆ isCategory:Fiber = {!!}
      isCategory.assoc-l-◆ isCategory:Fiber = {!!}
      isCategory.assoc-r-◆ isCategory:Fiber = {!!}
      isCategory._◈_ isCategory:Fiber = {!!}

  -- Fiber : (p : Fibration ℰ ℬ) -> Functor (ℬ ᵒᵖ) (𝐂𝐚𝐭 _)
  -- Fiber p = F since {!!}
  --   where
  --     F : ⟨ ℬ ⟩ -> Category _
  --     F b = Fb since {!!}
  --       where
  --         Fb : 𝒰 _
  --         Fb = ∑ λ (e : ⟨ ℰ ⟩) -> ⟨ p ⟩ e ≡ b




