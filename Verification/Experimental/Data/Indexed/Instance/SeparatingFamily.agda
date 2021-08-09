
module Verification.Experimental.Data.Indexed.Instance.SeparatingFamily where

open import Verification.Conventions

open import Verification.Experimental.Set.Setoid.Definition
open import Verification.Experimental.Set.Decidable
open import Verification.Experimental.Category.Std.Category.Definition
open import Verification.Experimental.Category.Std.Morphism.Iso
open import Verification.Experimental.Category.Std.Functor.Adjoint
open import Verification.Experimental.Data.Universe.Definition
open import Verification.Experimental.Data.Product.Definition
open import Verification.Experimental.Data.Sum.Definition
open import Verification.Experimental.Category.Std.Category.Structured.SeparatingFamily
open import Verification.Experimental.Category.Std.Limit.Specific.Coproduct.Definition
open import Verification.Experimental.Data.Universe.Instance.Category

open import Verification.Experimental.Data.Universe.Definition
open import Verification.Experimental.Data.Universe.Everything
open import Verification.Experimental.Data.Indexed.Definition
open import Verification.Experimental.Data.Indexed.Xiix




module _ {𝒞 : Category 𝑖} {{_ : hasSeparatingFamily 𝑘 𝒞}} {{_ : hasInitial 𝒞}}
         {I : 𝒰 𝑘} {{_ : isDiscrete I}}
         where

  Separator-𝐈𝐱 : 𝒰 _
  Separator-𝐈𝐱 = (Separator × I)

  Fam : (i j : I) -> 𝒰 𝑘
  Fam i j = i ≣ j

  -- instance
  --   isDecFam:Fam : ∀{i} -> isDecFam (Fam i)
  --   isDecFam.isProp:DecFam isDecFam:Fam = {!!}
  --   isDecFam.decide-Fam isDecFam:Fam = {!!} -- λ a → _≟-Str_ _ _

  -- lift-obj : (a : ⟨ 𝒞 ⟩) -> (i : I) -> (def : 𝐈𝐱 I 𝒞)-> 𝐈𝐱 I 𝒞
  -- lift-obj a i def = indexed f
  --   where
  --     f : I -> ⟨ 𝒞 ⟩
  --     f j with (i ≟-Str j)
  --     ... | yes p = a
  --     ... | no ¬p = ix def j


  separator-𝐈𝐱 : Separator-𝐈𝐱 -> 𝐈𝐱 I 𝒞
  separator-𝐈𝐱 (s , i) = 𝑥𝑖ₗ i (separator s)
  -- indexed f
  --     where
  --       f : I -> ⟨ 𝒞 ⟩
  --       f j with (i ≟-Str j)
  --       ... | yes p = separator s
  --       ... | no ¬p = ⊥

  -- into-separator-𝐈𝐱 : ∀{a : 𝐈𝐱 I 𝒞} 

  private
    sep = separator-𝐈𝐱
    Sep = Separator-𝐈𝐱

    lift-fromsep : ∀{a : Separator} {b : 𝐈𝐱 I 𝒞} -> {i : I} -> separator a ⟶ ix b i -> sep (a , i) ⟶ b
    lift-fromsep ϕ {i} = free ϕ {i}

    lem-1 : ∀{a : Separator} {b c : 𝐈𝐱 I 𝒞} -> {i j : I} -> i ≣ j -> (ξ : separator a ⟶ ix b i) -> (f g : b ⟶ c) -> lift-fromsep {b = b} ξ {j} ◆ f ∼ lift-fromsep {b = b} ξ {j} ◆ g -> ξ ◆ f ∼ ξ ◆ g
    lem-1 = ?
    -- lem-1 {i = i} {j} i≣j ξ f g p with (i ≟-Str j)
    -- ... | yes refl-≣ = p
    -- ... | no ¬p = 𝟘-rec (¬p i≣j)

    -- lem-1 : ∀{a : Separator} {b c : 𝐈𝐱 I 𝒞} -> {i j : I} -> i ≣ j -> (ξ : separator a ⟶ ix b i) -> (f g : b ⟶ c) -> lift-fromsep {b = b} ξ {j} ◆ f ∼ lift-fromsep {b = b} ξ {j} ◆ g -> ξ ◆ f ∼ ξ ◆ g
    -- lem-1 {i = i} {j} i≣j ξ f g p with (i ≟-Str j)
    -- ... | yes refl-≣ = p
    -- ... | no ¬p = 𝟘-rec (¬p i≣j)

{-

  instance
    isSeparatingFamily:sep : isSeparatingFamily (𝐈𝐱 I 𝒞) sep
    isSeparatingFamily.separate isSeparatingFamily:sep {a = a} {b} ϕ ψ p {i} = P
      where
        P : ϕ ∼ ψ
        P = separate ϕ ψ (λ {i = s} ξ →
                     let ξ' = lift-fromsep {b = a} ξ
                         G = p {i = (s , i)} ξ' {i}
                     in lem-1 refl-≣ ξ ϕ ψ G )


  instance
    hasSeparatingFamily:𝐈𝐱 : hasSeparatingFamily 𝑘 (𝐈𝐱 I 𝒞)
    hasSeparatingFamily.Separator hasSeparatingFamily:𝐈𝐱 = Sep
    hasSeparatingFamily.separator hasSeparatingFamily:𝐈𝐱 = sep
    hasSeparatingFamily.isSeparatingFamily:seperators hasSeparatingFamily:𝐈𝐱 = it




-}



