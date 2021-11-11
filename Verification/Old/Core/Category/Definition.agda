
module Verification.Old.Core.Category.Definition where

open import Verification.Conventions

--------------------------------------------------------------------------------
-- == Basic definitions

-- We define categories, functors and natural transformations.

--------------------------------------------------------------------------------
--  Categories

-- We define categories using hom-setoids as in "Proof_-relevant Category Theory in Agda"
-- (see: https://arxiv.org/pdf/2005.07059.pdf)
-- This is because this way we do not have to restrict ourselves to requiring the hom-types to be h-sets,
-- and can work mostly without doing truncations / requiring a certain hLevel.
--
-- (Problems would happen in slice categories and categories of_ cones, where equations become part of_ our morphisms)
--
-- We also copy other 'tricks' of_ them, as, e.g. requiring left and right associativity proof_s, and an id ◆ id ≣ id proof_.


-- [Definition]
-- | Given a type $𝒞$, whose elements we are going to call /objects/, we say that it has the structure of a category [...] if
--   the following additional data is given:
record isCategory (𝒞 : 𝒰 𝑖) (𝑗 : 𝔏 ^ 2) : 𝒰 (𝑖 ､ 𝑗 ⁺) where

-- | 1. A type family [..], assigning to every pair of objects |a b : 𝒞|
--      a type of /homomorphisms/ |Hom a b| between them.
--      We call elements of this type also simply /morphisms/ or /arrows/.
  field Hom : 𝒞 -> 𝒞 -> 𝒰 (𝑗 ⌄ 0)

-- | 2. A type family [..] on all hom-types, assigning to a pair of arrows |f g : Hom a b|
--      a type of equality proofs |f ≣ g| between them. This need not be the path equality |f ≡ g|,
--      thus we require that the family is at least an equivalence relation:
        _≣_           : ∀{a b : 𝒞} -> Hom a b -> Hom a b -> 𝒰 (𝑗 ⌄ 1)
        ⦃ isEquivRel:≣ ⦄  : ∀{a b : 𝒞} -> isEquivRel (_≣_ {a = a} {b = b})

-- | 3. An operation [..], assigning to every object |a| an identity morphism on this object.
        id : ∀{a : 𝒞} -> Hom a a

-- | 4. A composition operation [..], which allows us to compose morphisms whose domain and codomain are compatible.
        _◆_ : ∀{a b c : 𝒞} -> Hom a b -> Hom b c -> Hom a c

-- | 5. Proofs that |id| is a unit for composition.
        unit-l-◆          : ∀{a b : 𝒞} -> ∀{f : Hom a b} -> id ◆ f ≣ f
        unit-r-◆          : ∀{a b : 𝒞} -> ∀{f : Hom a b} -> f ◆ id ≣ f
        unit-2-◆          : ∀{a : 𝒞} -> id ◆ id ≣ id {a = a}
-- | 6. Proofs that composition is associative.
        assoc-l-◆         : ∀{a b c d : 𝒞} -> ∀{f : Hom a b} -> ∀{g : Hom b c} -> ∀{h : Hom c d} -> (f ◆ g) ◆ h ≣ f ◆ (g ◆ h)
        assoc-r-◆         : ∀{a b c d : 𝒞} -> ∀{f : Hom a b} -> ∀{g : Hom b c} -> ∀{h : Hom c d} -> f ◆ (g ◆ h) ≣ (f ◆ g) ◆ h
-- | 7. A proof that composition is compatible with the equivalence relation.
        _◈_               : ∀{a b c : 𝒞} -> ∀{f g : Hom a b} -> ∀{h i : Hom b c} -> f ≣ g -> h ≣ i -> f ◆ h ≣ g ◆ i

  infixl 50 _◆_ _◈_
-- //


open isCategory ⦃...⦄ public
unquoteDecl Category category = #struct "Cat" (quote isCategory) "𝒞" Category category


-- [Notation]
-- | We set [..], i.e., we may also write |a ⟶ b| for |Hom a b|.
_⟶_ = Hom
infixr 40 _⟶_
-- //




-- [Hide]
-- | A small category is one where all objects, arrows, and equivalence relations live in $𝒰₀$
SmallCategory = Category (ℓ₀ , ℓ₀ , ℓ₀)
ISmallCategory : (𝒞 : 𝒰₀) -> 𝒰₁
ISmallCategory 𝒞 = isCategory 𝒞 (ℓ₀ , ℓ₀)
-- //


--------------------------------------------------------------------------------
-- Functors

-- [Definition]
-- | Let [..] and [..] be two categories.
module _ (𝒞 : Category 𝑖) (𝒟 : Category 𝑗) where

-- |> A function |F|, mapping objects of |𝒞| to objects of |𝒟|
--    is called a functor [...] if the following additional data is given:
  record IFunctor (F : ⟨ 𝒞 ⟩ -> ⟨ 𝒟 ⟩) : 𝒰 (𝑖 ､ 𝑗 ⌄ 1 ､ 𝑗 ⌄ 2) where

          -- | - An operation [..] mapping arrows of |𝒞| to arrows in |𝒟|.
    field map : ∀{a b : ⟨ 𝒞 ⟩} -> Hom a b -> Hom (F a) (F b)

          -- | - A proof that |map| preserves identity morphisms.
          functoriality-id : ∀{a : ⟨ 𝒞 ⟩} -> map (id {a = a}) ≣ id {a = F a}

          -- | - A proof that |map| respects composition.
          functoriality-◆ : ∀{a b c : ⟨ 𝒞 ⟩} -> ∀{f : Hom a b} -> ∀{g : Hom b c} -> map (f ◆ g) ≣ (map f) ◆ (map g)

          -- | - A proof that |map| respects equivalence.
          functoriality-≣ : ∀{a b : ⟨ 𝒞 ⟩} -> ∀{f g : Hom a b} -> f ≣ g -> map f ≣ map g
-- //

open IFunctor {{...}} public

unquoteDecl Functor functor = #struct "Fun" (quote IFunctor) "F" Functor functor






--------------------------------------------------------------------------------
-- Natural Transformations



-- [Definition]
-- | Let [..], [..] be again two categories,
module _ {𝒞 : Category 𝑖} {𝒟 : Category 𝑗} where
-- |> and [..] two parallel functors between them.
  module _ (F G : Functor 𝒞 𝒟) where

-- |> A family of morphisms |α|, where for every |x : 𝒞|, |α ⌄ x : F x ⟶ G x| is an arrow in |𝒟|,
--   is called a *natural transformation* from |F| to |G|,
    record INatural (α : ∀{x : ⟨ 𝒞 ⟩} -> ⟨ F ⟩ x ⟶ ⟨ G ⟩ x) : 𝒰 (𝑖 ､ 𝑗 ⌄ 2) where

-- |> if it is natural, i.e., the following equation holds:
      field naturality : ∀{x y : ⟨ 𝒞 ⟩} -> ∀(f : x ⟶ y) -> α ◆ map {{of G}} f ≣ map {{of F}} f ◆ α

    open INatural {{...}} public
-- //

unquoteDecl Natural natural = #struct "Nat" (quote INatural) "α" Natural natural

