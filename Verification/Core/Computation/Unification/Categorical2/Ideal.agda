
module Verification.Core.Computation.Unification.Categorical2.Ideal where

open import Verification.Conventions
open import Verification.Core.Set.Setoid
open import Verification.Core.Order.Preorder
open import Verification.Core.Order.Lattice
open import Verification.Core.Order.WellFounded.Definition
open import Verification.Core.Data.Universe.Definition
open import Verification.Core.Data.Universe.Instance.Category
open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Category.Std.Category.Sized.Definition
open import Verification.Core.Category.Std.Morphism.Epi.Definition
open import Verification.Core.Category.Std.Category.As.ZeroMorphismCategory.Definition


-- module _ {𝑖} {𝒞 : 𝒰 _} {{_ : 𝐙𝐌𝐂𝐚𝐭 𝑖 on 𝒞}} where
  -- UpFamily : (a : 𝒞) -> 𝒰 _
  -- UpFamily a = ∀{b : 𝒞} -> (a ⟶ b) -> 𝒰 (𝑖)

-- ===* Ideals in categories with zero morphisms


-- | Fix a category |𝒞| with zero morphisms for the remainder of the chapter.
-- [Hide]
module _ {𝑖} {𝒞 : 𝒰 _} {{_ : 𝐙𝐌𝐂𝐚𝐭 𝑖 on 𝒞}} where
-- //
  -- |> We denote objects of |𝒞| usually simply by |a|, |b| or |c|.
  --   Most of the following statements concerning ideals
  --   are rather easy consequences
  --   of the definitions, and we mostly just give an informal sketch
  --   of the proofs.
  private variable a b c : 𝒞

  -- [Definition]
  -- | Let [..] be a fixed object of |𝒞|. A subset of arrows, all with source |a|,
  --   is encoded by a type family [..]. We call such a family a /right ideal
  --   at/ |a| if the following two conditions hold:
  module _ (a : 𝒞) (P : ∀{b : 𝒞} -> (f : a ⟶ b) -> 𝒰 𝑖) where
  -- | {}[]
    record isIdeal : 𝒰 𝑖 where
      -- | 1. Given any arrow |f| in this set, i.e. |P f| holds,
      --      then for any other arrow |g|, the composition |f ◆ g|
      --      is still in this set.
      field ideal-r-◆ : {f : a ⟶ b} -> P f -> (g : b ⟶ c) -> P (f ◆ g)

      -- | 2. All zero arrows are in this set.
      field ideal-pt : ∀{b} -> P {b} pt

      -- | 3. We further require that if two arrow are equal
      --      with regards to the equivalence relation,
      --      it cannot happen that one of them is in |P|
      --      while the other one is not.
      field transp-Ideal : {f g : a ⟶ b} -> (p : f ∼ g) -> P f -> P g

    -- |: A /left ideal/ could be defined by reversing arrows.
    --    Since we only need ideals in the direction as defined above,
    --    we usually skip the qualifier and simply speak of ideals.

    open isIdeal {{...}} public
  -- //

  -- [Hide]
  module _ (a : 𝒞) where
    Idealᵘ = _ :& isIdeal a
    macro Ideal = #structureOn Idealᵘ

  -- //


  -- | {}[]
  module _ {a : 𝒞} where

    -- [Definition]
    -- | We define an equivalence relation on ideals.
    --   Let [..] be two ideals at a.
    module _ (A B : Ideal a) where
      -- |> We say that |A ∼ B| [] if the following can be shown:
      record _∼-Ideal_ : 𝒰 (𝑖) where
        constructor incl
        field ⟨_⟩ : ∀(f : a ⟶ b) -> ⟨ A ⟩ f ↔ ⟨ B ⟩ f
        -- |> That is, two ideals are to be considered equivalent
        --    if they contain the same arrows.

    -- //

    -- [Lemma]
    -- | This relation on ideals is indeed an equivalence relation.

    -- //

    -- [Proof]
    -- | Note that to prove |⟨ A ⟩ f ↔ ⟨ B ⟩ f|, one
    --   has to give two functions, one converting a proof of
    --   membership in |A| to a proof of membership in |B|,
    --   and one vice versa. Thus reflexivity is shown by the
    --   identity function, symmetry by switching the directions
    --   of the two given functions, and transitivity by composition.

    -- //

    open _∼-Ideal_ public
    -- _∼-Ideal_ : (A B : Ideal a) -> 𝒰 _
    -- _∼-Ideal_ A B = ∀{b} -> (f : a ⟶ b) -> ⟨ A ⟩ f ↔ ⟨ B ⟩ f

-- [Hide]
    private
      lem-1 : ∀{A : Ideal a} -> A ∼-Ideal A
      lem-1 = incl λ f → (id , id)

      lem-2 : ∀{A B : Ideal a} -> A ∼-Ideal B -> B ∼-Ideal A
      lem-2 P = incl λ f → ⟨ P ⟩ f .snd , ⟨ P ⟩ f .fst

      lem-3 : ∀{A B C : Ideal a} -> A ∼-Ideal B -> B ∼-Ideal C -> A ∼-Ideal C
      lem-3 P Q = incl λ f → ⟨ P ⟩ f .fst ◆ ⟨ Q ⟩ f .fst , ⟨ Q ⟩ f .snd ◆ ⟨ P ⟩ f .snd


    instance
      isSetoid:Ideal : isSetoid (Ideal a)
      isSetoid:Ideal = isSetoid:byDef (_∼-Ideal_) lem-1 lem-2 lem-3

    -- //



    -- [Definition]
    -- | We define a preorder on ideals.
    --   Let [..] be two ideals at a.
    module _ (A B : Ideal a) where
      -- |> We say that |A ≤ B| [] if the following can be shown:
      record _≤-Ideal_ : 𝒰 (𝑖) where
        constructor incl
        field ⟨_⟩ : (f : a ⟶ b) -> ⟨ A ⟩ f -> ⟨ B ⟩ f

      -- |> This merely expresses the fact that |A| is a subset of |B|.

    open _≤-Ideal_ public
    -- //

    -- [Lemma]
    -- | This relation on ideals is indeed a preorder.

    -- //

    -- [Proof]
    -- | Very similar to the proof of REF. Reflexivity and transitivity
    --   is shown using the identity function and composition of functions.
    --   The fact that |∼| is compatible with |≤| is also shown by composition.

    -- //

-- [Hide]
    reflexive-Ideal : ∀{A : Ideal a} -> A ≤-Ideal A
    reflexive-Ideal = incl λ f P → P

    _⟡-Ideal_ : ∀{A B C : Ideal a} -> A ≤-Ideal B -> B ≤-Ideal C -> A ≤-Ideal C
    _⟡-Ideal_ P Q = incl λ f → ⟨ P ⟩ f ◆ ⟨ Q ⟩ f

    transp-≤-Ideal : ∀{A B C D : Ideal a} -> (A ∼ B) -> (C ∼ D) -> A ≤-Ideal C -> B ≤-Ideal D
    transp-≤-Ideal p q r = incl λ f → ⟨ p ⟩ f .snd ◆ ⟨ r ⟩ f ◆ ⟨ q ⟩ f .fst

    instance
      isPreorder:Ideal : isPreorder _ (Ideal a)
      isPreorder:Ideal = record
        { _≤_ = _≤-Ideal_
        ; reflexive = reflexive-Ideal
        ; _⟡_ = _⟡-Ideal_
        ; transp-≤ = transp-≤-Ideal
        }

      isPartialorder:Ideal : isPartialorder (Ideal a)
      isPartialorder:Ideal = record { antisym = λ p q → incl λ f → ⟨ p ⟩ f , ⟨ q ⟩ f }


-- //
