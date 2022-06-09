
-- {-# OPTIONS --syntactic-equality=0 #-}

module Verification.Core.Category.Std.Category.Structured.Monoidal.Definition2 where

open import Verification.Conventions
open import Verification.Core.Set.Setoid
open import Verification.Core.Data.Product.Definition
open import Verification.Core.Data.Lift.Definition
open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Category.Std.Category.Instance.Category
open import Verification.Core.Category.Std.Category.Instance.FiniteProductCategory
open import Verification.Core.Category.Std.Category.Construction.Product
open import Verification.Core.Category.Std.Category.Instance.ProductMonoid
open import Verification.Core.Category.Std.Limit.Specific.Product
open import Verification.Core.Category.Std.Limit.Specific.Product.Instance.Functor
open import Verification.Core.Category.Std.Category.Instance.ProductMonoid
open import Verification.Core.Category.Std.Functor.Definition
open import Verification.Core.Category.Std.Functor.Constant
open import Verification.Core.Category.Std.Functor.Instance.Category
open import Verification.Core.Category.Std.Natural.Definition
open import Verification.Core.Category.Std.Natural.Iso
open import Verification.Core.Category.Std.Morphism.Iso
open import Verification.Core.Category.Std.Category.Structured.FiniteProduct.Definition


-- aaa = unit-l-×

module _ {𝒞 : 𝒰 𝑗} {{_ : isCategory {𝑖} 𝒞}} {{_ : hasFiniteProducts ′ 𝒞 ′}} where

  private instance
    _ : isSetoid 𝒞
    _ = isSetoid:byCategory

    -- TODO: Why is it necessary to create this local instance?
    _ = isSetoidHom:⧼⧽

  -- TODO: embed these ones in the proofs below
  unit-l-⊓ : ∀{a : 𝒞} -> a ⊓ ⊤ ⟶ a
  unit-l-⊓ = π₀

  ₗυ : ∀{a : 𝒞} -> a ⟶ ⊤ ⊓ a
  ₗυ = ⧼ intro-⊤ , id ⧽

  [_]ₗυc : ∀{a : 𝒞} -> (⊤ ⟶ a) -> a ⟶ a ⊓ a
  [_]ₗυc f = ⧼ intro-⊤ ◆ f , id ⧽


{-
record isMonoidal (𝒞 : Category 𝑖) : 𝒰 𝑖 where
  field [⊗]ᵘ : ⟨ 𝒞 ⟩ ×-𝒰 ⟨ 𝒞 ⟩ -> ⟨ 𝒞 ⟩
  field [Id]ᵘ : ⟨ ⊤-𝐂𝐚𝐭 {𝑖} ⟩ -> ⟨ 𝒞 ⟩
  field unit-l-⊗ : ∀(a) -> [⊗]ᵘ ([Id]ᵘ (lift tt) , a) ⟶ a

  field isFunctor:[⊗] : isFunctor (𝒞 ×-𝐂𝐚𝐭 𝒞) 𝒞 [⊗]ᵘ
  field isFunctor:[Id] : isFunctor (⊤-𝐂𝐚𝐭) 𝒞 [Id]ᵘ

  [⊗] : Functor (𝒞 ×-𝐂𝐚𝐭 𝒞) 𝒞
  [⊗] = [⊗]ᵘ since isFunctor:[⊗]

  [Id] : Functor ⊤-𝐂𝐚𝐭 𝒞
  [Id] = [Id]ᵘ since isFunctor:[Id]

  -- field isNatural:unit-l-⊗ : isNatural ([ [Id] ]ₗυc ◆-𝐂𝐚𝐭 [⊗]) id-𝐂𝐚𝐭 unit-l-⊗
  field isNatural:unit-l-⊗ : isNatural (⧼ intro-⊤ ◆ [Id] , id-𝐂𝐚𝐭 {𝒞 = 𝒞} ⧽ ◆-𝐂𝐚𝐭 [⊗]) id-𝐂𝐚𝐭 unit-l-⊗
-}


record MonoidalType (𝒞 : Category 𝑖) : 𝒰 𝑖 where
  field [⊗] : Functor (𝒞 ×-𝐂𝐚𝐭 𝒞) 𝒞
  field [Id] : Functor (⊤-𝐂𝐚𝐭 {𝑖}) 𝒞

open MonoidalType {{...}} public

module _ {𝒞 : Category 𝑖} {{_ : MonoidalType 𝒞}} where
  ⊗- : ∀{𝒳 : Category 𝑗} -> Functor 𝒳 (𝒞 ×-𝐂𝐚𝐭 𝒞) -> Functor 𝒳 𝒞
  ⊗- F = F ◆-𝐂𝐚𝐭 [⊗]

  postulate cong-⊗ : ∀{𝒳 : Category 𝑖} {F G : Functor 𝒳 (𝒞 ×-𝐂𝐚𝐭 𝒞)}
                  -> F ≅ G -> ⊗- F ≅ ⊗- G


  !Id : ∀{𝒳 : Category 𝑗} -> Functor 𝒳 𝒞
  !Id = intro-⊤-𝐂𝐚𝐭 ◆-𝐂𝐚𝐭 [Id]

module _ {𝒞 : Category 𝑖} {𝒟 : Category 𝑗} {ℰ : Category 𝑘} where
  α-𝐂𝐚𝐭 : Functor ((𝒞 ×-𝐂𝐚𝐭 𝒟) ×-𝐂𝐚𝐭 ℰ) (𝒞 ×-𝐂𝐚𝐭 (𝒟 ×-𝐂𝐚𝐭 ℰ))
  α-𝐂𝐚𝐭 = {!!}

module _ {𝒞 : Category 𝑖} {𝒟 : Category 𝑗} {ℰ : Category 𝑘} {ℱ : Category 𝑙} where
  _⇃⊓⇂-𝐂𝐚𝐭_ : Functor 𝒞 𝒟 -> Functor ℰ ℱ -> Functor (𝒞 ×-𝐂𝐚𝐭 ℰ) (𝒟 ×-𝐂𝐚𝐭 ℱ)
  _⇃⊓⇂-𝐂𝐚𝐭_ = {!!}

module _ {𝒞 : Category 𝑖} where -- {𝒟 : Category 𝑗} where
  -- s-𝐂𝐚𝐭 : Functor (𝒞 ×-𝐂𝐚𝐭 𝒟) (𝒟 ×-𝐂𝐚𝐭 𝒞)
  -- s-𝐂𝐚𝐭 = ⧼ π₁-𝐂𝐚𝐭 , π₀-𝐂𝐚𝐭 ⧽-𝐂𝐚𝐭

  -- τ-𝐂𝐚𝐭 : ∀{𝒳 : Category 𝑘}
  --         -> {F : Functor 𝒳 (𝒞 ×-𝐂𝐚𝐭 𝒟)}
  --         -> {G : Functor 𝒳 (𝒟 ×-𝐂𝐚𝐭 𝒞)}
  --         -> F ◆-𝐂𝐚𝐭 s-𝐂𝐚𝐭 ≅ G
  -- τ-𝐂𝐚𝐭 = {!!}

  τ-𝐂𝐚𝐭 : ∀{𝒳 : Category 𝑘}
          -> {F : Functor 𝒳 (𝒞)}
          -> {G : Functor 𝒳 (𝒞)}
          -> ⧼ F , G ⧽-𝐂𝐚𝐭 ≅ ⧼ G , F ⧽-𝐂𝐚𝐭
  τ-𝐂𝐚𝐭 = {!!}

private
  ⧼_⧽⃨ = ⧼_⧽-𝐂𝐚𝐭
  _◆⃨_ = _◆-𝐂𝐚𝐭_
  id⃨ = id-𝐂𝐚𝐭
  τ⃨ = τ-𝐂𝐚𝐭

module _ {𝒞 : Category 𝑖} {𝒟 : Category 𝑗} {ℰ : Category 𝑘} where
  NaturalOverLeft : (Functor 𝒞 𝒟) -> (Functor 𝒞 ℰ) -> Functor 𝒟 ℰ -> 𝒰 _
  NaturalOverLeft Over F G = Natural F (Over ◆-𝐂𝐚𝐭 G)

record MonoidalFunc {𝒞 : Category 𝑖} (𝒞ᵗ : MonoidalType 𝒞) : 𝒰 𝑖 where
  private instance _ = 𝒞ᵗ

  field unit-l-⊗ : (⊗- ⧼ !Id , id⃨ ⧽⃨) ≅ id⃨
  field unit-r-⊗ : (⊗- ⧼ id⃨ , !Id ⧽⃨) ≅ id⃨
  field assoc-l-⊗ : NaturalOverLeft α-𝐂𝐚𝐭
                            (⊗-(⊗-( id⃨ ⇃⊓⇂-𝐂𝐚𝐭 id⃨) ⇃⊓⇂-𝐂𝐚𝐭 id⃨))
                            (⊗-(id⃨ ⇃⊓⇂-𝐂𝐚𝐭 ⊗-( id⃨ ⇃⊓⇂-𝐂𝐚𝐭 id⃨)))

  -- field triangle-⊗ : ((sym-≅ unit-l-⊗ ∙-≅ cong-⊗ (τ-𝐂𝐚𝐭 {F = !Id} {G = id⃨})) ∙-≅ unit-r-⊗) ≡ (id-𝐅𝐮𝐧𝐜 since {!!})
  -- field triangle-⊗ : unit-l-⊗ ∙-≅ 


  -- field isIso:unit-l-⊗ : isIso _ _ unit-l-⊗
                            -- {!(α-𝐂𝐚𝐭 ◆-𝐂𝐚𝐭 (⊗- ⧼ id-𝐂𝐚𝐭 , ⊗- ⧼ id-𝐂𝐚𝐭 , id-𝐂𝐚𝐭 ⧽-𝐂𝐚𝐭 ⧽-𝐂𝐚𝐭))!}


  -- unitᵘ-l-⊗ : ∀(a : ⟨ 𝒞 ⟩) -> ⟨ [⊗] ⟩ (⟨ [Id] ⟩ (lift tt) , a) ⟶ a
  -- unitᵘ-l-⊗ = ⟨ unit-l-⊗ ⟩


  -- field unit-l-⊗ : ∀(a) -> [⊗]ᵘ ([Id]ᵘ (lift tt) , a) ⟶ a


