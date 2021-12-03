
module Verification.Core.Data.List.Variant.FreeMonoid.Definition where


open import Verification.Core.Conventions hiding (ℕ)
open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Category.Std.Functor.Definition
open import Verification.Core.Data.Universe.Definition
open import Verification.Core.Data.Universe.Instance.Category
open import Verification.Core.Set.Decidable
open import Verification.Core.Set.Setoid.Definition
open import Verification.Core.Set.Setoid.Free
open import Verification.Core.Set.Function.Injective
open import Verification.Core.Data.Prop.Definition
open import Verification.Core.Data.Nat.Definition
open import Verification.Core.Data.Nat.Instance.Monoid
open import Verification.Core.Data.List.Variant.Base.Definition
open import Verification.Core.Data.List.Variant.Base.Instance.Monoid
open import Verification.Core.Algebra.Monoid.Definition
open import Verification.Core.Set.Contradiction

-- #Notation/Rewrite# incl = \iota

----------------------------------------------------------
-- The free encoding

-- [Definition]
-- | The type [..] is defined as a data type with the following
-- constructors:
data ⋆List (A : 𝒰 𝑖) : 𝒰 𝑖 where
  -- | - An inclusion [..].
  incl : A -> ⋆List A

  -- | - Free multiplication [..].
  _⋆-⧜_ : (a b : ⋆List A) -> ⋆List A

  -- | - Free unit [..].
  ◌-⧜ : ⋆List A
-- //

-- [Hide]

{-# DISPLAY _⋆-⧜_ a b = a ⋆ b #-}
{-# DISPLAY ◌-⧜ = ◌ #-}


macro
  𝖥𝗋𝖾𝖾-𝐌𝐨𝐧 : (A : 𝒰 𝑖) -> SomeStructure
  𝖥𝗋𝖾𝖾-𝐌𝐨𝐧 A = #structureOn (⋆List A)

module _ {A : 𝒰 𝑖} where


  -- the setoid and monoid structure

  infix 10 _∼-⋆List_
  data _∼-⋆List_ : (a b : ⋆List A) -> 𝒰 𝑖 where
    unit-l-⋆-⧜  : ∀{a} -> ◌-⧜ ⋆-⧜ a ∼-⋆List a
    unit-r-⋆-⧜  : ∀{a} -> a ⋆-⧜ ◌-⧜ ∼-⋆List a
    assoc-l-⋆-⧜ : ∀{a b c} -> (a ⋆-⧜ b) ⋆-⧜ c ∼-⋆List a ⋆-⧜ (b ⋆-⧜ c)
    cong-l-⋆-⧜  : ∀{a b c} -> (a ∼-⋆List b) -> (a ⋆-⧜ c ∼-⋆List b ⋆-⧜ c)
    cong-r-⋆-⧜  : ∀{a b c} -> (b ∼-⋆List c) -> (a ⋆-⧜ b ∼-⋆List a ⋆-⧜ c)

  private
    lem-1 : ∀{a c d} ->  (q : RST _∼-⋆List_ c d) -> RST _∼-⋆List_ (a ⋆-⧜ c) (a ⋆-⧜ d)
    lem-1 (incl x) = incl (cong-r-⋆-⧜ x)
    lem-1 refl-RST = refl-RST
    lem-1 (sym-RST q) = sym-RST (lem-1 q)
    lem-1 (p ∙-RST q) = lem-1 p ∙-RST lem-1 q

  cong-⋆-⧜ : ∀{a b c d} -> (p : RST _∼-⋆List_ a b) (q : RST _∼-⋆List_ c d) -> RST _∼-⋆List_ (a ⋆-⧜ c) (b ⋆-⧜ d)
  cong-⋆-⧜ (incl x) q     = incl (cong-l-⋆-⧜ x) ∙-RST lem-1 q
  cong-⋆-⧜ refl-RST q     = lem-1 q
  cong-⋆-⧜ (sym-RST p) q  = sym-RST (cong-⋆-⧜ p (sym-RST q))
  cong-⋆-⧜ (p ∙-RST p') q = cong-⋆-⧜ p q ∙-RST cong-⋆-⧜ p' refl-RST

  instance
    isSetoid:⋆List : isSetoid (⋆List A)
    isSetoid:⋆List = isSetoid:byFree _∼-⋆List_

    isMonoid:⋆List : isMonoid (𝖥𝗋𝖾𝖾-𝐌𝐨𝐧 A)
    isMonoid:⋆List = record
                          { _⋆_        = _⋆-⧜_
                          ; ◌          = ◌-⧜
                          ; unit-l-⋆   = incl unit-l-⋆-⧜
                          ; unit-r-⋆   = incl unit-r-⋆-⧜
                          ; assoc-l-⋆  = incl assoc-l-⋆-⧜
                          ; _≀⋆≀_ = cong-⋆-⧜
                          }


  -- the element relation

  data _∍_ : ⋆List A -> A -> 𝒰 𝑖 where
    incl : ∀{x} -> incl x ∍ x
    right-∍ : ∀{a b x} -> b ∍ x -> (a ⋆ b) ∍ x
    left-∍ : ∀{a b x} -> a ∍ x -> (a ⋆ b) ∍ x

  instance
    isInjective-𝒰:left-∍ : ∀{a b x} -> isInjective-𝒰 (left-∍ {a} {b} {x})
    isInjective-𝒰.cancel-injective-𝒰 (isInjective-𝒰:left-∍ {a} {b} {x}) {m1} {m2} p = λ i -> f (p i) m1
      where f : (p : a ⋆ b ∍ x) -> a ∍ x -> a ∍ x
            f (left-∍ p) def = p
            f (right-∍ p) def = def

    isInjective-𝒰:right-∍ : ∀{a b x} -> isInjective-𝒰 (right-∍ {a} {b} {x})
    isInjective-𝒰:right-∍ {a} {b} {x} = injective (λ {m1} {m2} p i → f (p i) m1)
      where f : (p : a ⋆ b ∍ x) -> b ∍ x -> b ∍ x
            f (left-∍ p) def = def
            f (right-∍ p) def = p

  instance
    isContradiction:left-∍≡right-∍ : ∀{a b x} -> {p : a ∍ x} -> {q : b ∍ x} -> isContradiction (left-∍ p ≡ right-∍ q)
    isContradiction:left-∍≡right-∍ {a} {b} {x} {p} {q} = contradiction (λ r → transport (cong P r) tt)
      where P : (a ⋆ b ∍ x) -> 𝒰₀
            P (left-∍ a) = ⊤-𝒰
            P (right-∍ a) = ⊥-𝒰

    isContradiction:right-∍≡left-∍ : ∀{a b x} -> {p : a ∍ x} -> {q : b ∍ x} -> isContradiction (right-∍ p ≡ left-∍ q)
    isContradiction:right-∍≡left-∍ = contradiction (λ x → contradict (λ i -> (x (~ i))))

  -- the element relation is discrete
  instance
    isDiscrete:∍ : ∀{as a} -> isDiscrete (as ∍ a)
    isDiscrete._≟-Str_ (isDiscrete:∍ {as} {a}) = h
      where
        -- TODO prove this part with the additional fact that A is a set (needs to be added).
        g : ∀{a b} -> (p : a ≡ b) -> (x : incl b ∍ a) -> PathP (λ i -> incl (p i) ∍ a) incl x
        g p incl = {!!}

        f : ∀{as a} -> (x y : as ∍ a) -> Decision (x ≡ y)
        f incl y = yes (g refl-≡ y)
        f (right-∍ x) (right-∍ y) with f x y
        ... | yes p = yes (cong right-∍ p)
        ... | no ¬p = no (λ q -> ¬p (cancel-injective-𝒰 q))
        f (right-∍ x) (left-∍ y) = no impossible
        f (left-∍ x) (right-∍ y) = no impossible
        f (left-∍ x) (left-∍ y) with f x y
        ... | yes p = yes (cong left-∍ p)
        ... | no ¬p = no (λ q -> ¬p (cancel-injective-𝒰 q))

        h : ∀{as a} -> (x y : as ∍ a) -> Decision (x ≣ y)
        h x y with f x y
        ... | yes p = yes (≡→≡-Str p)
        ... | no ¬p = no (λ q -> ¬p (≡-Str→≡ q))

  -- the inclusion from lists
  ι-⋆List : List A -> ⋆List A
  ι-⋆List ⦋⦌ = ◌
  ι-⋆List (a ∷ as) = incl a ⋆ ι-⋆List as

  instance
    hasInclusion:List,⋆List : hasInclusion (List A) (⋆List A)
    hasInclusion:List,⋆List = inclusion ι-⋆List

  pres-⋆-ι-⋆List : ∀{as bs : List A} -> ι (as ⋆ bs) ∼ ι as ⋆ ι bs
  pres-⋆-ι-⋆List {⦋⦌} {bs} = unit-l-⋆ ⁻¹
  pres-⋆-ι-⋆List {x ∷ as} {bs} = refl ≀⋆≀ pres-⋆-ι-⋆List ∙ assoc-r-⋆

  -- the normalization into lists
  ♮-⋆List : ⋆List A -> List A
  ♮-⋆List (incl x) = x ∷ []
  ♮-⋆List (a ⋆-⧜ b) = ♮-⋆List a ⋆ ♮-⋆List b
  ♮-⋆List ◌-⧜ = ⦋⦌

  instance
    hasNormalization:⋆List,List : hasNormalization (⋆List A) (List A)
    hasNormalization:⋆List,List = normalization ♮-⋆List

  surj-♮-⋆List : ∀{a : ⋆List A} -> ι (♮ a) ∼ a
  surj-♮-⋆List {incl x} = unit-r-⋆
  surj-♮-⋆List {a ⋆-⧜ a₁} = pres-⋆-ι-⋆List ∙ surj-♮-⋆List ≀⋆≀ surj-♮-⋆List
  surj-♮-⋆List {◌-⧜} = refl

  injective-♮-⋆List : ∀{a b : ⋆List A} -> ♮ a ≡ ♮ b -> a ∼ b
  injective-♮-⋆List p = surj-♮-⋆List ⁻¹ ∙ ≡→∼ (cong ι p) ∙ surj-♮-⋆List




module _ {A : 𝒰 𝑖} {B : 𝒰 _} {{_ : B is Monoid 𝑗}} where
  rec-⋆List : (f : A -> B) -> ⋆List A -> B
  rec-⋆List f (incl x)           = f x
  rec-⋆List f (a ⋆-⧜ b)  = rec-⋆List f a ⋆ rec-⋆List f b
  rec-⋆List f ◌-⧜        = ◌

  instance
    Notation:hasRec:⋆List : Notation:hasRec (A -> B) (⋆List A -> B)
    Notation:hasRec:⋆List = record { rec = rec-⋆List }

module _ {A : 𝒰 𝑖} {B : 𝒰 𝑗} where
  map-⋆List : (A -> B) -> ⋆List A -> ⋆List B
  map-⋆List f (incl x) = incl (f x)
  map-⋆List f (as ⋆-⧜ bs) = map-⋆List f as ⋆-⧜ map-⋆List f bs
  map-⋆List f ◌-⧜ = ◌-⧜


instance
  isFunctor:⋆List : isFunctor (𝐔𝐧𝐢𝐯 𝑖) (𝐔𝐧𝐢𝐯 𝑖) ⋆List
  isFunctor.map isFunctor:⋆List = map-⋆List
  isFunctor.isSetoidHom:map isFunctor:⋆List = {!!}
  isFunctor.functoriality-id isFunctor:⋆List = {!!}
  isFunctor.functoriality-◆ isFunctor:⋆List = {!!}

module _ {A : 𝒰 𝑖} {B : 𝒰 𝑗} where
  map-∍ : (f : A -> B) -> {as : ⋆List A} {a : A} -> as ∍ a -> map-⋆List f as ∍ f a
  map-∍ f incl = incl
  map-∍ f (right-∍ x) = right-∍ (map-∍ f x)
  map-∍ f (left-∍ x) = left-∍ (map-∍ f x)


-- length of lists

module _ {A : 𝒰 𝑖} where
  人length : ∀(a : ⋆List A) -> ℕ
  人length = rec-⋆List (const 1)


-----------------------------------------
-- we can decide whether an element is in a list

module _ {A : 𝒰 𝑖} {{_ : isDiscrete A}} where
  find-first-∍ : ∀ (xs : ⋆List A) -> (x : A) -> isDecidable (xs ∍ x)
  find-first-∍ (incl y) x with x ≟-Str y
  ... | yes refl-≣ = just incl
  ... | no ¬p = left λ {incl → impossible (¬p refl-≣)}
  find-first-∍ (xs ⋆-⧜ ys) x with find-first-∍ xs x | find-first-∍ ys x
  ... | left ¬xs∍x | left ¬ys∍x = left λ { (left-∍ xs∍x) → ¬xs∍x xs∍x
                                         ; (right-∍ ys∍x) → ¬ys∍x ys∍x
                                         }
  ... | left ¬xs∍x | just ys∍x = just (right-∍ ys∍x)
  ... | just xs∍x | Y = right (left-∍ xs∍x)
  find-first-∍ ◌-⧜ x = left λ ()

-- //
