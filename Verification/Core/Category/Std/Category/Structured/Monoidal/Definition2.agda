
-- {-# OPTIONS --syntactic-equality=1 #-}

{-# OPTIONS --warning=noInstanceWithExplicitArg #-}


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
open import Verification.Core.Category.Std.Category.Instance.2Category
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


module _ {𝒞 : Category 𝑖} {𝒟 : Category 𝑗} {ℰ : Category 𝑘} {ℱ : Category 𝑙} where
  postulate
    _⇃⊓⇂-𝐂𝐚𝐭_ : Functor 𝒞 𝒟 -> Functor ℰ ℱ -> Functor (𝒞 ×-𝐂𝐚𝐭 ℰ) (𝒟 ×-𝐂𝐚𝐭 ℱ)
  -- _⇃⊓⇂-𝐂𝐚𝐭_ = {!!}

module _ {𝒞 : Category 𝑖} {𝒟 : Category 𝑗} {ℰ : Category 𝑘} where
  α-𝐂𝐚𝐭 : Functor ((𝒞 ×-𝐂𝐚𝐭 𝒟) ×-𝐂𝐚𝐭 ℰ) (𝒞 ×-𝐂𝐚𝐭 (𝒟 ×-𝐂𝐚𝐭 ℰ))
  α-𝐂𝐚𝐭 = {!!}

private
  ⧼_⧽⃨ = ⧼_⧽-𝐂𝐚𝐭
  infixl 40 _◆⃨_
  _◆⃨_ = _◆-𝐂𝐚𝐭_
  id⃨ = id-𝐂𝐚𝐭
  id⋮ = id-𝐂𝐚𝐭
  π₀⋮ = π₀-𝐂𝐚𝐭
  π₁⋮ = π₁-𝐂𝐚𝐭


record MonoidalType (𝒞 : Category 𝑖) : 𝒰 𝑖 where
  field [⊗] : Functor (𝒞 ×-𝐂𝐚𝐭 𝒞) 𝒞
  field [Id] : Functor (⊤-𝐂𝐚𝐭 {𝑖}) 𝒞

open MonoidalType {{...}} public


module _ {𝒞 : Category 𝑖} {{_ : MonoidalType 𝒞}} where
  ⊗- : ∀{𝒳 : Category 𝑗} -> Functor 𝒳 (𝒞 ×-𝐂𝐚𝐭 𝒞) -> Functor 𝒳 𝒞
  ⊗- F = F ◆-𝐂𝐚𝐭 [⊗]

  module _ {𝒳 𝒴 : Category 𝑗} where
    postulate
      _⊗_ : (F : Functor 𝒳 𝒞) -> (G : Functor 𝒴 𝒞) -> Functor (𝒳 ×-𝐂𝐚𝐭 𝒴) 𝒞

    module _ {F F' : Functor 𝒳 𝒞} {G G' : Functor 𝒴 𝒞} where
      postulate
        _≀⊗≀_ : F ≅ F' -> G ≅ G' -> (F ⊗ G) ≅ (F' ⊗ G')

  module _ {𝒳 𝒴 𝒵₀ 𝒵₁ : Category 𝑗} where
    postulate
      factor-◆-⊗ : {A₀ : Functor 𝒵₀ 𝒳} {A₁ : Functor 𝒵₁ 𝒴}
                   -> {F : Functor 𝒳 𝒞} -> {G : Functor 𝒴 𝒞}
                   -> ((A₀ ◆⃨ F) ⊗ (A₁ ◆⃨ G)) ≅ (A₀ ⇃⊓⇂-𝐂𝐚𝐭 A₁) ◆⃨ (F ⊗ G)

    -- _⊗_ F G = (F ⇃⊓⇂-𝐂𝐚𝐭 G) ◆-𝐂𝐚𝐭 [⊗]

        -- _≀⊗≀_ F G = {!!}

  postulate cong-⊗ : ∀{𝒳 : Category 𝑖} {F G : Functor 𝒳 (𝒞 ×-𝐂𝐚𝐭 𝒞)}
                  -> F ≅ G -> ⊗- F ≅ ⊗- G

  -- _⊗_ : ∀{𝒳 𝒴 : Category 𝑗} -> (F : Functor 𝒳 𝒞) -> (G : Functor 𝒴 𝒞) -> Functor (𝒳 ×-𝐂𝐚𝐭 𝒴) 𝒞
  -- _⊗_ F G = (F ⇃⊓⇂-𝐂𝐚𝐭 G) ◆-𝐂𝐚𝐭 [⊗]


  !Id : ∀{𝒳 : Category 𝑗} -> Functor 𝒳 𝒞
  !Id = intro-⊤-𝐂𝐚𝐭 ◆-𝐂𝐚𝐭 [Id]

  Id = [Id]


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


  -- idᶜ 

module _ {𝒞 : Category 𝑖} {𝒟 : Category 𝑗} {ℰ : Category 𝑘} where
  NaturalOverLeft : (Functor 𝒞 𝒟) -> (Functor 𝒞 ℰ) -> Functor 𝒟 ℰ -> 𝒰 _
  NaturalOverLeft Over F G = Natural F (Over ◆-𝐂𝐚𝐭 G)

record MonoidalFunc {𝒞 : Category 𝑖} (𝒞ᵗ : MonoidalType 𝒞) : 𝒰 (𝑖 ⁺) where
  private instance _ = 𝒞ᵗ

  field unit-l-⊗ : ∀{X : Category 𝑖} -> ∀(F : Functor X 𝒞) -> (Id ⊗ F) ≅ π₁⋮ ◆⃨ F
  field unit-r-⊗ : ∀{X : Category 𝑖} -> ∀(F : Functor X 𝒞) -> (F ⊗ Id) ≅ π₀⋮ ◆⃨ F
  field assoc-l-⊗ : ∀{𝒳 𝒴 𝒵 : Category 𝑖}
                    -> ∀{F : Functor 𝒳 𝒞}
                    -> ∀{G : Functor 𝒴 𝒞}
                    -> ∀{H : Functor 𝒵 𝒞}
                    -> ((F ⊗ G) ⊗ H) ≅ α-𝐂𝐚𝐭 ◆⃨ (F ⊗ (G ⊗ H))

open MonoidalFunc {{...}} public


-- record MonoidalFunc {𝒞 : Category 𝑖} (𝒞ᵗ : MonoidalType 𝒞) : 𝒰 (𝑖 ⁺) where
module _ {𝒞 : Category 𝑖} {{𝒞ᵗ : MonoidalType 𝒞}} {{𝒞ᶠ : MonoidalFunc 𝒞ᵗ}} where

  lhs : ∀{𝒳 𝒴 : Category 𝑖} -> {F : Functor 𝒳 𝒞} {G : Functor 𝒴 𝒞}
      -- -> ((F ⊗ Id) ⊗ G) ≅ ((π₀⋮ ◆⃨ F) ⊗ (id⋮ ◆⃨ G))
      -> ((F ⊗ Id) ⊗ G) ≅ ((π₀⋮ ⇃⊓⇂-𝐂𝐚𝐭 id⋮ {𝒞 = 𝒴}) ◆⃨ (F ⊗ G))
  lhs {F = F} {G} = (unit-r-⊗ F ≀⊗≀ sym-≅ (unit-l-◆-𝐂𝐚𝐭 {F = G})) ∙-≅ factor-◆-⊗

  rhs : ∀{𝒳 𝒴 : Category 𝑖} -> {F : Functor 𝒳 𝒞} {G : Functor 𝒴 𝒞}
      -- -> ((F ⊗ Id) ⊗ G) ≅ ((π₀⋮ ◆⃨ F) ⊗ (id⋮ ◆⃨ G))
      -> _
  rhs {F = F} {G = G}
    = ((F ⊗ Id) ⊗ G)            ⟨ assoc-l-⊗ {F = F} {Id} {G} ⟩-≅
      α-𝐂𝐚𝐭 ◆⃨ (F ⊗ (Id ⊗ G))    ⟨ refl-≅ {A = α-𝐂𝐚𝐭} ≀◆≀-𝐂𝐚𝐭 (refl-≅ {A = F} ≀⊗≀ unit-l-⊗ G) ⟩-≅
      α-𝐂𝐚𝐭 ◆⃨ (F ⊗ (π₁⋮ ◆⃨ G))    ∎-≅


    -- ((F ⊗ Id) ⊗ G) ≅ ((π₀⋮ ⇃⊓⇂-𝐂𝐚𝐭 id⋮ {𝒞 = 𝒴}) ◆⃨ (F ⊗ G))


    -- let X = unit-r-⊗ {F = F}
    --     Y : G ≅ (id ◆⃨ G)
    --     Y = sym-≅ unit-l-◆-𝐂𝐚𝐭
    -- in _≀⊗≀_ X Y


  -- (unit-r-⊗ {F = F} ≀⊗≀ refl-≅ {A = G})

  -- field triangle-⊗ : (refl-≅ ≀⊗≀ unit-l-⊗) ∙-≅ {!!} ≡ assoc-l-⊗ ∙-≅ ?


  --⊗- ⧼ !Id , id⃨ ⧽⃨) ≅ id⃨

-- record MonoidalFunc {𝒞 : Category 𝑖} (𝒞ᵗ : MonoidalType 𝒞) : 𝒰 𝑖 where
--   private instance _ = 𝒞ᵗ

--   field unit-l-⊗ : (⊗- ⧼ !Id , id⃨ ⧽⃨) ≅ id⃨
--   field unit-r-⊗ : (⊗- ⧼ id⃨ , !Id ⧽⃨) ≅ id⃨
--   field assoc-l-⊗ : NaturalOverLeft α-𝐂𝐚𝐭
--                             (⊗-(⊗-( id⃨ ⇃⊓⇂-𝐂𝐚𝐭 id⃨) ⇃⊓⇂-𝐂𝐚𝐭 id⃨))
--                             (⊗-(id⃨ ⇃⊓⇂-𝐂𝐚𝐭 ⊗-( id⃨ ⇃⊓⇂-𝐂𝐚𝐭 id⃨)))





  -- field triangle-⊗ : ((sym-≅ unit-l-⊗ ∙-≅ cong-⊗ (τ-𝐂𝐚𝐭 {F = !Id} {G = id⃨})) ∙-≅ unit-r-⊗) ≡ (id-𝐅𝐮𝐧𝐜 since {!!})
  -- field triangle-⊗ : unit-l-⊗ ∙-≅ 


  -- field isIso:unit-l-⊗ : isIso _ _ unit-l-⊗
                            -- {!(α-𝐂𝐚𝐭 ◆-𝐂𝐚𝐭 (⊗- ⧼ id-𝐂𝐚𝐭 , ⊗- ⧼ id-𝐂𝐚𝐭 , id-𝐂𝐚𝐭 ⧽-𝐂𝐚𝐭 ⧽-𝐂𝐚𝐭))!}


  -- unitᵘ-l-⊗ : ∀(a : ⟨ 𝒞 ⟩) -> ⟨ [⊗] ⟩ (⟨ [Id] ⟩ (lift tt) , a) ⟶ a
  -- unitᵘ-l-⊗ = ⟨ unit-l-⊗ ⟩


  -- field unit-l-⊗ : ∀(a) -> [⊗]ᵘ ([Id]ᵘ (lift tt) , a) ⟶ a


