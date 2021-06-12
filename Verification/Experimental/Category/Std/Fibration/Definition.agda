
module Verification.Experimental.Category.Std.Fibration.Definition where

open import Verification.Experimental.Conventions

open import Verification.Experimental.Set.Setoid.Definition
open import Verification.Experimental.Set.Set.Definition
open import Verification.Experimental.Set.Set.Instance.Category
open import Verification.Experimental.Category.Std.Category.Definition
open import Verification.Experimental.Category.Std.Functor.Definition
open import Verification.Experimental.Category.Std.Category.Opposite
open import Verification.Experimental.Category.Std.Morphism.Iso
open import Verification.Experimental.Category.Std.Category.Instance.Category
open import Verification.Experimental.Category.Std.Limit.Specific.Pullback

open import Verification.Experimental.Data.Universe.Definition
open import Verification.Experimental.Data.Universe.Everything

--
-- The definition of (Grothendieck) fibrations
-- (following the definition at https://ncatlab.org/nlab/show/Grothendieck+fibration)
--

cong₂-Str : ∀{A : 𝒰 𝑖} {B : 𝒰 𝑗} {C : 𝒰 𝑘} -> (f : A -> B -> C) -> {a1 a2 : A} -> {b1 b2 : B} -> (p : a1 ≣ a2) -> (q : b1 ≣ b2) -> f a1 b1 ≣ f a2 b2
cong₂-Str f refl-StrId refl-StrId = refl-StrId

-- private variable
  -- ℬ : Category 𝑖
  -- ℰ : Category 𝑗
  -- e e₀ e₁ e₂ : ⟨ ℰ ⟩


-- module _  where
-- record FullSubsetoid (X : Setoid 𝑖) (ϕ : ⟨ X ⟩ -> 𝒰 𝑗) : 𝒰 𝑖 where
--   field 


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

module _ {𝒞 : 𝒰 _} {{_ : Category 𝑖 on 𝒞}} where
  pid : {a b : 𝒞} -> (a ≣ b) -> a ≅ b
  pid refl-StrId = ⟨ refl {{isEquivRel:≅}} ⟩


module _ {ℰ : Category 𝑗} {ℬ : Category 𝑖} where

  module _ (p : Fibration ℰ ℬ) (b : ⟨ ℬ ⟩) where
    record isFiber (e : Obj ℰ) : 𝒰 (𝑗 ､ 𝑖) where
      constructor isfiber
      field isSectionFiber : ⟨ p ⟩ ⟨ e ⟩ ≣ b

    open isFiber public

    Fiber = _ :& isFiber

  instance
    isFiber:Refl : ∀{p : Fibration ℰ ℬ} {e : ⟨ ℰ ⟩} -> isFiber p (⟨ p ⟩ e) (obj e)
    isFiber:Refl = isfiber refl

  module _ {p : Fibration ℰ ℬ} {b : ⟨ ℬ ⟩} where

    private
      p' : Functor ℰ ℬ
      p' = ′ ⟨ p ⟩ ′

      record isFiberHom (e₀ e₁ : Fiber p b) (ϕ : ⟨ e₀ ⟩ ⟶ ⟨ e₁ ⟩) : 𝒰 (𝑖 ､ 𝑗) where
        constructor isfiberhom
        field isSectionFiberHom : ⟨ iso-inv (pid (isSectionFiber (of e₀))) ⟩ ◆ (map {{of p'}} ϕ) ◆ ⟨ pid (isSectionFiber (of e₁)) ⟩ ∼ id

      open isFiberHom {{...}} public

      FiberHom : ∀(e₀ e₁ : Fiber p b) -> 𝒰 _
      FiberHom e₀ e₁ = _ :& isFiberHom e₀ e₁

      -- FiberHom : ∀(e₀ e₁ : Fiber p b) -> 𝒰 _
      -- FiberHom e₀ e₁ = ∑ λ (ϕ : ⟨ e₀ ⟩ ⟶ ⟨ e₁ ⟩) -> ⟨ iso-inv (pid (isSectionFiber (of e₀))) ⟩ ◆ (map {{of p'}} ϕ) ◆ ⟨ pid (isSectionFiber (of e₁)) ⟩ ∼ id

      -- FiberHom : ∀(e₀ e₁ : Fiber p b) -> 𝒰 _
      -- FiberHom e₀ e₁ = ∑ λ (ϕ : ⟨ e₀ ⟩ ⟶ ⟨ e₁ ⟩) -> ⟨ iso-inv (pid (isSectionFiber (of e₀))) ⟩ ◆ (map {{of p'}} ϕ) ◆ ⟨ pid (isSectionFiber (of e₁)) ⟩ ∼ id

      -- transport-Str (cong₂-Str (_⟶_) (isSectionFiber (of e₀)) (isSectionFiber (of e₁))) (map {{of p'}} ϕ) ∼ id

      -- (λ i -> isSectionFiber (of e₀) i ⟶ isSectionFiber (of e₁) i) (map {{of p'}} ϕ) ∼ id
      -- FiberHom e₀ e₁ = ∑ λ (ϕ : ⟨ e₀ ⟩ ⟶ ⟨ e₁ ⟩) -> transport (λ i -> isSectionFiber (of e₀) i ⟶ isSectionFiber (of e₁) i) (map {{of p'}} ϕ) ∼ id

      instance
        isSetoid:FiberHom : ∀{e₀ e₁} -> isSetoid _ (Hom-Base FiberHom e₀ e₁)
        isSetoid:FiberHom {e₀} {e₁} = isSetoid:Hom-Base {{isSetoid:FullSubsetoid (′ ⟨ e₀ ⟩ ⟶ ⟨ e₁ ⟩ ′) ⟨_⟩}}

      id-Fiber : ∀{e : Fiber p b} -> FiberHom e e
      id-Fiber {e} = id since isfiberhom P
        where P : _ ◆ map id ◆ _ ∼ id
              P = _ ◆ map id ◆ _     ⟨ refl ◈ functoriality-id ◈ refl ⟩-∼
                  _ ◆ id ◆ _         ⟨ unit-r-◆ ◈ refl ⟩-∼
                  _ ◆ _              ⟨ inv-l-◆ (of (pid (isSectionFiber (of e)))) ⟩-∼
                  id                 ∎

      comp-Fiber : ∀{e f g : Fiber p b} -> FiberHom e f -> FiberHom f g -> FiberHom e g
      comp-Fiber {′ e ′} {f} {′ g ′} (ϕ') (ψ') = ϕ ◆ ψ since isfiberhom P
        where β = pid (isSectionFiber (of f))
              ϕ = ⟨ ϕ' ⟩
              ψ = ⟨ ψ' ⟩

              P : (_ ◆ map (ϕ ◆ ψ) ◆ _) ∼ id
              P = _ ◆ map (ϕ ◆ ψ) ◆ _                 ⟨ refl ◈ functoriality-◆ ◈ refl ⟩-∼
                  _ ◆ (map ϕ ◆ map ψ) ◆ _             ⟨ refl ◈ (unit-r-◆ ⁻¹ ◈ refl) ◈ refl  ⟩-∼
                  _ ◆ (map ϕ ◆ id ◆ map ψ) ◆ _        ⟨ refl ◈ (refl ◈ inv-r-◆ (of β) ⁻¹ ◈ refl) ◈ refl ⟩-∼
                  _ ◆ (map ϕ ◆ (_ ◆ _) ◆ map ψ) ◆ _   ⟨ refl ◈ (assoc-r-◆ ◈ refl) ◈ refl ⟩-∼
                  _ ◆ ((map ϕ ◆ _) ◆ _ ◆ map ψ) ◆ _   ⟨ refl ◈ (assoc-l-◆) ◈ refl ⟩-∼
                  _ ◆ ((map ϕ ◆ _) ◆ (_ ◆ map ψ)) ◆ _ ⟨ assoc-r-◆ ◈ refl ⟩-∼
                  (_ ◆ (map ϕ ◆ _)) ◆ (_ ◆ map ψ) ◆ _ ⟨ (assoc-r-◆ ∙ isSectionFiberHom {{of ϕ'}}) ◈ refl ◈ refl ⟩-∼
                  id ◆ (_ ◆ map ψ) ◆ _                ⟨ unit-l-◆ ◈ refl ⟩-∼
                  (_ ◆ map ψ) ◆ _                     ⟨ isSectionFiberHom {{of ψ'}} ⟩-∼
                  id                      ∎

    instance
      isCategory:Fiber : isCategory _ (Fiber p b)
      isCategory.Hom' isCategory:Fiber = FiberHom
      isCategory.isSetoid:Hom isCategory:Fiber = it
      isCategory.id isCategory:Fiber {e} = incl (id-Fiber {e})
      isCategory._◆_ isCategory:Fiber ϕ ψ = incl (comp-Fiber ⟨ ϕ ⟩ ⟨ ψ ⟩)
      isCategory.unit-l-◆ isCategory:Fiber = incl unit-l-◆
      isCategory.unit-r-◆ isCategory:Fiber = incl unit-r-◆
      isCategory.unit-2-◆ isCategory:Fiber = incl unit-2-◆
      isCategory.assoc-l-◆ isCategory:Fiber = incl assoc-l-◆
      isCategory.assoc-r-◆ isCategory:Fiber = incl assoc-r-◆
      isCategory._◈_ isCategory:Fiber = {!!}

  FiberF : (p : Fibration ℰ ℬ) -> Functor (ℬ ᵒᵖ) (𝐂𝐚𝐭 _)
  FiberF p = F since it
    where
      F : ⟨ ℬ ⟩ -> Category _
      F b = ′ Fiber p b ′

      Ff : ∀{a b : ⟨ ℬ ⟩} (f : a ⟶ b) -> Fiber p b -> Fiber p a
      Ff f e = {!!}

      instance
        isFunctor:F : isFunctor (ℬ ᵒᵖ) (𝐂𝐚𝐭 _) F
        isFunctor.map isFunctor:F = λ x → {!!}
        isFunctor.isSetoidHom:map isFunctor:F = {!!}
        isFunctor.functoriality-id isFunctor:F = {!!}
        isFunctor.functoriality-◆ isFunctor:F = {!!}




