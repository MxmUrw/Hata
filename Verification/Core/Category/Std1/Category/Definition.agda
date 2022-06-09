
{-# OPTIONS --warning=noInstanceWithExplicitArg #-}

module Verification.Core.Category.Std1.Category.Definition where

open import Verification.Conventions
-- open import Verification.Core.Set.Setoid


record CategoryType (𝑖 : 𝔏 ^ 3) : 𝒰 (𝑖 ⁺) where
  constructor [_,_,_]
  field Cell₀ᵈ : 𝒰 (𝑖 ⌄ 0)
  field Cell₁ᵈ : Cell₀ᵈ -> Cell₀ᵈ -> 𝒰 (𝑖 ⌄ 1)
  field Cell₂ᵈ : ∀{a b : Cell₀ᵈ} -> (f g : Cell₁ᵈ a b) -> 𝒰 (𝑖 ⌄ 2)

  _₁⟶_ = Cell₁ᵈ
  _₂⟶_ = Cell₂ᵈ

-- open CategoryType public

open CategoryType {{...}} hiding (Cell₀ᵈ) public
open CategoryType using (Cell₀ᵈ) public

record CategoryFun {𝑖 : 𝔏 ^ 3} (𝒞ᵗ : CategoryType 𝑖) : 𝒰 (𝑖) where
  instance _ = 𝒞ᵗ
  field id₁ᵈ : ∀{a : Cell₀ᵈ 𝒞ᵗ} -> Cell₁ᵈ a a
  field id₂ᵈ : ∀{a b : Cell₀ᵈ 𝒞ᵗ} -> {f : Cell₁ᵈ a b} -> Cell₂ᵈ f f

  field compᵈ₁₁ : ∀{a b c : Cell₀ᵈ 𝒞ᵗ} -> (Cell₁ᵈ a b ×-𝒰 Cell₁ᵈ b c) -> Cell₁ᵈ a c
  field _₁◆ᵈ₁_ : ∀{a b c : Cell₀ᵈ 𝒞ᵗ} -> (f : Cell₁ᵈ a b) -> (g : Cell₁ᵈ b c) -> Cell₁ᵈ a c

  -- constructor [_,_,_∣_,_∣_,_,_]
  -- field Cell₀ᵈ : 𝒰 (𝑖 ⌄ 0)
  -- field Cell₁ᵈ : Cell₀ᵈ -> Cell₀ᵈ -> 𝒰 (𝑖 ⌄ 1)
  -- field Cell₂ᵈ : ∀{a b : Cell₀ᵈ} -> (f g : Cell₁ᵈ a b) -> 𝒰 (𝑖 ⌄ 2)

open CategoryFun {{...}} public

record CategoryEq {𝑖 : 𝔏 ^ 3} {𝒞ᵗ : CategoryType 𝑖} (𝒞ᶠ : CategoryFun 𝒞ᵗ) : 𝒰 𝑖 where
  instance _ = 𝒞ᵗ
  instance _ = 𝒞ᶠ
  field unit-l-◆ : ∀{a b : Cell₀ᵈ 𝒞ᵗ} {f : a ₁⟶ b} -> (id₁ᵈ ₁◆ᵈ₁ f) ₂⟶ f

record is1Category {𝑖 : 𝔏 ^ 2} {𝑗 : 𝔏} (𝒞 : 𝒰 𝑗) : 𝒰 (𝑗 ⊔ 𝑖 ⁺) where
  field Hom : 𝒞 -> 𝒞 -> 𝒰 (𝑖 ⌄ 0)
  field _∼_ : ∀{a b : 𝒞} -> (f g : Hom a b) -> 𝒰 (𝑖 ⌄ 1)
  -- field Cells : CategoryType 𝑖
  field Funs : CategoryFun ([ 𝒞 , Hom , _∼_ ])
  field Eqs : CategoryEq (Funs)


open is1Category ⦃...⦄ public

1Category : (𝑗 : 𝔏 ^ 3) -> 𝒰 _
1Category 𝑗 = 𝒰 (𝑗 ⌄ 0) :& is1Category {𝑗 ⌄ 1 ⋯ 2}

HomOf : (𝒞 : 1Category 𝑖) -> (a b : ⟨ 𝒞 ⟩) -> 𝒰 _
HomOf 𝒞 a b = Hom a b

IsoOf : (𝒞 : 1Category 𝑖) -> (a b : ⟨ 𝒞 ⟩) -> 𝒰 _
IsoOf 𝒞 a b = Hom a b ×-𝒰 Hom b a

ObjOf : (𝒞 : 1Category 𝑖) -> 𝒰 _
ObjOf 𝒞 = ⟨ 𝒞 ⟩

module _ (𝒞 : 1Category 𝑖) (𝒟 : 1Category 𝑗) where
  isFunctor : (f : ⟨ 𝒞 ⟩ -> ⟨ 𝒟 ⟩) -> 𝒰 (𝑖 ､ 𝑗)
  isFunctor = {!!}

_×-1𝐂𝐚𝐭_ : 1Category 𝑖 -> 1Category 𝑖 -> 1Category 𝑖
_×-1𝐂𝐚𝐭_ 𝒞 𝒟 = ⟨ 𝒞 ⟩ ×-𝒰 ⟨ 𝒟 ⟩ since {!!}


record is2Category {𝑖 : 𝔏 ^ 3} {𝑗 : 𝔏} (𝒞 : 𝒰 𝑗) : 𝒰 (𝑗 ⊔ 𝑖 ⁺) where
  field Cells : 𝒞 -> 𝒞 -> 1Category 𝑖
  field Funs₀ : CategoryFun [ 𝒞 , (λ a b -> ObjOf (Cells a b)) , (IsoOf (Cells _ _)) ]
  field Eqs₀ : CategoryEq Funs₀


  field isFunctor:comp : ∀{a b c : 𝒞} -> isFunctor (Cells a b ×-1𝐂𝐚𝐭 Cells b c) (Cells a c) (compᵈ₁₁ {{Funs₀}})

  -- field funs₀ : CategoryFun [ 𝒞 , (λ a b -> Cell₀ᵈ (Cells a b)) , (λ a b -> Cell₁ᵈ {{Cells _ _}} a b) ]
  -- field eqs₀ : CategoryEq funs₀

{-
  _₁⟶_ = Cell₁ᵈ
  _₂⟶_ = Cell₂ᵈ

  field id₁ᵈ : ∀{a : Cell₀ᵈ} -> Cell₁ᵈ a a
  field id₂ᵈ : ∀{a b : Cell₀ᵈ} -> {f : Cell₁ᵈ a b} -> Cell₂ᵈ f f

  field _₁◆ᵈ₁_ : ∀{a b c : Cell₀ᵈ} -> (f : Cell₁ᵈ a b) -> (g : Cell₁ᵈ b c) -> Cell₁ᵈ a c
  field _₂◆ᵈ₁_ : ∀{a b c : Cell₀ᵈ}
                 -> {f f' : Cell₁ᵈ a b}
                 -> {g g' : Cell₁ᵈ b c}
                 -> (α : Cell₂ᵈ f f') -> (β : Cell₂ᵈ g g')
                 -> Cell₂ᵈ (f ₁◆ᵈ₁ g) (f' ₁◆ᵈ₁ g')
  field _₂◆ᵈ₂_ : ∀{a b : Cell₀ᵈ} -> {f g h : Cell₁ᵈ a b} -> Cell₂ᵈ f g -> Cell₂ᵈ g h -> Cell₂ᵈ f h

open ≥1CategoryData {{...}} hiding (Cell₀ᵈ ; Cell₁ᵈ ; Cell₂ᵈ) public
open ≥1CategoryData using (Cell₀ᵈ ; Cell₁ᵈ ; Cell₂ᵈ) public


record is≥1Category {𝑖 : 𝔏 ^ 3} (𝒞ᵈ : ≥1CategoryData 𝑖) : 𝒰 (𝑖) where
  instance _ = 𝒞ᵈ
  field unit-l-◆ : ∀{a b : Cell₀ᵈ 𝒞ᵈ} {f : a ₁⟶ b} -> (id₁ᵈ ₁◆ᵈ₁ f) ₂⟶ f

record ≥2CategoryData (𝑖 : 𝔏 ^ 4) : 𝒰 (𝑖 ⁺) where
  field Cell₀ᵈ : 𝒰 (𝑖 ⌄ 0)
  field Cells : Cell₀ᵈ -> ≥1CategoryData (𝑖 ⌄ 1 ⋯ 3)
-}



{-
record isCategory {𝑗 : 𝔏 ^ 2} {𝑖 : 𝔏} (𝒞 : 𝒰 𝑖) : 𝒰 ((𝑖 ⌄ 0) ⊔ 𝑗 ⁺) where
  constructor category
  infixl 50 _◆_ _◈_

-- | 1. A type family [..], assigning to every pair of objects |a b : 𝒞|
--      a type of /homomorphisms/ |Hom a b| between them.
--      We call elements of this type also simply /morphisms/ or /arrows/.
  field Hom : 𝒞 -> 𝒞 -> 𝒰 (𝑗 ⌄ 0)

  -- Hom : 𝒞 -> 𝒞 -> 𝒰 (𝑗 ⌄ 0)
  -- Hom a b = Hom-Base Hom' a b
  field {{isSetoid:Hom}} : ∀{a b : 𝒞} -> isSetoid {𝑗 ⌄ 1} (Hom a b)

-- | 3. An operation [..], assigning to every object |a| an identity morphism on this object.
  field id : ∀{a : 𝒞} -> Hom a a

-- | 4. A composition operation [..], which allows us to compose morphisms whose domain and codomain are compatible.
        _◆_ : ∀{a b c : 𝒞} -> Hom a b -> Hom b c -> Hom a c

-- | 5. Proofs that |id| is a unit for composition.
        unit-l-◆          : ∀{a b : 𝒞} -> ∀{f : Hom a b} -> id ◆ f ∼ f
        unit-r-◆          : ∀{a b : 𝒞} -> ∀{f : Hom a b} -> f ◆ id ∼ f
        unit-2-◆          : ∀{a : 𝒞} -> id ◆ id ∼ id {a = a}
-- | 6. Proofs that composition is associative.
        assoc-l-◆         : ∀{a b c d : 𝒞} -> ∀{f : Hom a b} -> ∀{g : Hom b c} -> ∀{h : Hom c d} -> (f ◆ g) ◆ h ∼ f ◆ (g ◆ h)
        assoc-r-◆         : ∀{a b c d : 𝒞} -> ∀{f : Hom a b} -> ∀{g : Hom b c} -> ∀{h : Hom c d} -> f ◆ (g ◆ h) ∼ (f ◆ g) ◆ h
-- | 7. A proof that composition is compatible with the equivalence relation.
        _◈_               : ∀{a b c : 𝒞} -> ∀{f g : Hom a b} -> ∀{h i : Hom b c} -> f ∼ g -> h ∼ i -> f ◆ h ∼ g ◆ i

open isCategory ⦃...⦄ public

-}



