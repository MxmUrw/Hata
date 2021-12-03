
module Verification.Core.Algebra.Monoid.Free.Definition where


open import Verification.Core.Conventions hiding (ℕ)
open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Category.Std.Functor.Definition
open import Verification.Core.Data.Universe.Everything
open import Verification.Core.Set.Decidable
open import Verification.Core.Set.Setoid.Definition
open import Verification.Core.Set.Setoid.Free
open import Verification.Core.Set.Function.Injective
open import Verification.Core.Data.Prop.Definition
open import Verification.Core.Data.Nat.Definition
open import Verification.Core.Data.List.Definition
open import Verification.Core.Data.List.Instance.Monoid
open import Verification.Core.Algebra.Monoid.Definition
open import Verification.Core.Set.Contradiction



----------------------------------------------------------
-- The free encoding

-- [Definition]
-- | The type [..] is defined as a data type with the following
-- constructors:
data Free-𝐌𝐨𝐧 (A : 𝒰 𝑖) : 𝒰 𝑖 where
  -- | - An inclusion [..].
  incl : A -> Free-𝐌𝐨𝐧 A

  -- | - Free multiplication [..].
  _⋆-⧜_ : (a b : Free-𝐌𝐨𝐧 A) -> Free-𝐌𝐨𝐧 A

  -- | - Free unit [..].
  ◌-⧜ : Free-𝐌𝐨𝐧 A
-- //

-- [Hide]
pattern _⋆-Free-𝐌𝐨𝐧_ a b = a ⋆-⧜ b
pattern ◌-Free-𝐌𝐨𝐧 = ◌-⧜

{-# DISPLAY _⋆-Free-𝐌𝐨𝐧_ a b = a ⋆ b #-}
{-# DISPLAY ◌-Free-𝐌𝐨𝐧 = ◌ #-}


macro
  𝖥𝗋𝖾𝖾-𝐌𝐨𝐧 : (A : 𝒰 𝑖) -> SomeStructure
  𝖥𝗋𝖾𝖾-𝐌𝐨𝐧 A = #structureOn (Free-𝐌𝐨𝐧 A)

module _ {A : 𝒰 𝑖} where


  -- the setoid and monoid structure

  infix 10 _∼-Free-𝐌𝐨𝐧_
  data _∼-Free-𝐌𝐨𝐧_ : (a b : Free-𝐌𝐨𝐧 A) -> 𝒰 𝑖 where
    unit-l-⋆-Free-𝐌𝐨𝐧  : ∀{a} -> ◌-Free-𝐌𝐨𝐧 ⋆-Free-𝐌𝐨𝐧 a ∼-Free-𝐌𝐨𝐧 a
    unit-r-⋆-Free-𝐌𝐨𝐧  : ∀{a} -> a ⋆-Free-𝐌𝐨𝐧 ◌-Free-𝐌𝐨𝐧 ∼-Free-𝐌𝐨𝐧 a
    assoc-l-⋆-Free-𝐌𝐨𝐧 : ∀{a b c} -> (a ⋆-Free-𝐌𝐨𝐧 b) ⋆-Free-𝐌𝐨𝐧 c ∼-Free-𝐌𝐨𝐧 a ⋆-Free-𝐌𝐨𝐧 (b ⋆-Free-𝐌𝐨𝐧 c)
    cong-l-⋆-Free-𝐌𝐨𝐧  : ∀{a b c} -> (a ∼-Free-𝐌𝐨𝐧 b) -> (a ⋆-Free-𝐌𝐨𝐧 c ∼-Free-𝐌𝐨𝐧 b ⋆-Free-𝐌𝐨𝐧 c)
    cong-r-⋆-Free-𝐌𝐨𝐧  : ∀{a b c} -> (b ∼-Free-𝐌𝐨𝐧 c) -> (a ⋆-Free-𝐌𝐨𝐧 b ∼-Free-𝐌𝐨𝐧 a ⋆-Free-𝐌𝐨𝐧 c)

  private
    lem-1 : ∀{a c d} ->  (q : RST _∼-Free-𝐌𝐨𝐧_ c d) -> RST _∼-Free-𝐌𝐨𝐧_ (a ⋆-Free-𝐌𝐨𝐧 c) (a ⋆-Free-𝐌𝐨𝐧 d)
    lem-1 (incl x) = incl (cong-r-⋆-Free-𝐌𝐨𝐧 x)
    lem-1 refl-RST = refl-RST
    lem-1 (sym-RST q) = sym-RST (lem-1 q)
    lem-1 (p ∙-RST q) = lem-1 p ∙-RST lem-1 q

  cong-⋆-Free-𝐌𝐨𝐧 : ∀{a b c d} -> (p : RST _∼-Free-𝐌𝐨𝐧_ a b) (q : RST _∼-Free-𝐌𝐨𝐧_ c d) -> RST _∼-Free-𝐌𝐨𝐧_ (a ⋆-Free-𝐌𝐨𝐧 c) (b ⋆-Free-𝐌𝐨𝐧 d)
  cong-⋆-Free-𝐌𝐨𝐧 (incl x) q     = incl (cong-l-⋆-Free-𝐌𝐨𝐧 x) ∙-RST lem-1 q
  cong-⋆-Free-𝐌𝐨𝐧 refl-RST q     = lem-1 q
  cong-⋆-Free-𝐌𝐨𝐧 (sym-RST p) q  = sym-RST (cong-⋆-Free-𝐌𝐨𝐧 p (sym-RST q))
  cong-⋆-Free-𝐌𝐨𝐧 (p ∙-RST p') q = cong-⋆-Free-𝐌𝐨𝐧 p q ∙-RST cong-⋆-Free-𝐌𝐨𝐧 p' refl-RST

  instance
    isSetoid:Free-𝐌𝐨𝐧 : isSetoid (Free-𝐌𝐨𝐧 A)
    isSetoid:Free-𝐌𝐨𝐧 = isSetoid:byFree _∼-Free-𝐌𝐨𝐧_

    isMonoid:Free-𝐌𝐨𝐧 : isMonoid (𝖥𝗋𝖾𝖾-𝐌𝐨𝐧 A)
    isMonoid:Free-𝐌𝐨𝐧 = record
                          { _⋆_        = _⋆-Free-𝐌𝐨𝐧_
                          ; ◌          = ◌-Free-𝐌𝐨𝐧
                          ; unit-l-⋆   = incl unit-l-⋆-Free-𝐌𝐨𝐧
                          ; unit-r-⋆   = incl unit-r-⋆-Free-𝐌𝐨𝐧
                          ; assoc-l-⋆  = incl assoc-l-⋆-Free-𝐌𝐨𝐧
                          ; _≀⋆≀_ = cong-⋆-Free-𝐌𝐨𝐧
                          }


  -- the element relation

  data _∍_ : Free-𝐌𝐨𝐧 A -> A -> 𝒰 𝑖 where
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
  ι-Free-𝐌𝐨𝐧 : List A -> Free-𝐌𝐨𝐧 A
  ι-Free-𝐌𝐨𝐧 ⦋⦌ = ◌
  ι-Free-𝐌𝐨𝐧 (a ∷ as) = incl a ⋆ ι-Free-𝐌𝐨𝐧 as

  instance
    hasInclusion:List,Free-𝐌𝐨𝐧 : hasInclusion (List A) (Free-𝐌𝐨𝐧 A)
    hasInclusion:List,Free-𝐌𝐨𝐧 = inclusion ι-Free-𝐌𝐨𝐧

  pres-⋆-ι-Free-𝐌𝐨𝐧 : ∀{as bs : List A} -> ι (as ⋆ bs) ∼ ι as ⋆ ι bs
  pres-⋆-ι-Free-𝐌𝐨𝐧 {⦋⦌} {bs} = unit-l-⋆ ⁻¹
  pres-⋆-ι-Free-𝐌𝐨𝐧 {x ∷ as} {bs} = refl ≀⋆≀ pres-⋆-ι-Free-𝐌𝐨𝐧 ∙ assoc-r-⋆

  -- the normalization into lists
  ♮-Free-𝐌𝐨𝐧 : Free-𝐌𝐨𝐧 A -> List A
  ♮-Free-𝐌𝐨𝐧 (incl x) = x ∷ []
  ♮-Free-𝐌𝐨𝐧 (a ⋆-Free-𝐌𝐨𝐧 b) = ♮-Free-𝐌𝐨𝐧 a ⋆ ♮-Free-𝐌𝐨𝐧 b
  ♮-Free-𝐌𝐨𝐧 ◌-Free-𝐌𝐨𝐧 = ⦋⦌

  instance
    hasNormalization:Free-𝐌𝐨𝐧,List : hasNormalization (Free-𝐌𝐨𝐧 A) (List A)
    hasNormalization:Free-𝐌𝐨𝐧,List = normalization ♮-Free-𝐌𝐨𝐧

  surj-♮-Free-𝐌𝐨𝐧 : ∀{a : Free-𝐌𝐨𝐧 A} -> ι (♮ a) ∼ a
  surj-♮-Free-𝐌𝐨𝐧 {incl x} = unit-r-⋆
  surj-♮-Free-𝐌𝐨𝐧 {a ⋆-Free-𝐌𝐨𝐧 a₁} = pres-⋆-ι-Free-𝐌𝐨𝐧 ∙ surj-♮-Free-𝐌𝐨𝐧 ≀⋆≀ surj-♮-Free-𝐌𝐨𝐧
  surj-♮-Free-𝐌𝐨𝐧 {◌-Free-𝐌𝐨𝐧} = refl

  injective-♮-Free-𝐌𝐨𝐧 : ∀{a b : Free-𝐌𝐨𝐧 A} -> ♮ a ≡ ♮ b -> a ∼ b
  injective-♮-Free-𝐌𝐨𝐧 p = surj-♮-Free-𝐌𝐨𝐧 ⁻¹ ∙ ≡→∼ (cong ι p) ∙ surj-♮-Free-𝐌𝐨𝐧




module _ {A : 𝒰 𝑖} {B : 𝒰 _} {{_ : B is Monoid 𝑗}} where
  rec-Free-𝐌𝐨𝐧 : (f : A -> B) -> Free-𝐌𝐨𝐧 A -> B
  rec-Free-𝐌𝐨𝐧 f (incl x)           = f x
  rec-Free-𝐌𝐨𝐧 f (a ⋆-Free-𝐌𝐨𝐧 b)  = rec-Free-𝐌𝐨𝐧 f a ⋆ rec-Free-𝐌𝐨𝐧 f b
  rec-Free-𝐌𝐨𝐧 f ◌-Free-𝐌𝐨𝐧        = ◌

  instance
    Notation:hasRec:Free-𝐌𝐨𝐧 : Notation:hasRec (A -> B) (Free-𝐌𝐨𝐧 A -> B)
    Notation:hasRec:Free-𝐌𝐨𝐧 = record { rec = rec-Free-𝐌𝐨𝐧 }

module _ {A : 𝒰 𝑖} {B : 𝒰 𝑗} where
  map-Free-𝐌𝐨𝐧 : (A -> B) -> Free-𝐌𝐨𝐧 A -> Free-𝐌𝐨𝐧 B
  map-Free-𝐌𝐨𝐧 f (incl x) = incl (f x)
  map-Free-𝐌𝐨𝐧 f (as ⋆-Free-𝐌𝐨𝐧 bs) = map-Free-𝐌𝐨𝐧 f as ⋆-⧜ map-Free-𝐌𝐨𝐧 f bs
  map-Free-𝐌𝐨𝐧 f ◌-Free-𝐌𝐨𝐧 = ◌-⧜


instance
  isFunctor:Free-𝐌𝐨𝐧 : isFunctor (𝐔𝐧𝐢𝐯 𝑖) (𝐔𝐧𝐢𝐯 𝑖) Free-𝐌𝐨𝐧
  isFunctor.map isFunctor:Free-𝐌𝐨𝐧 = map-Free-𝐌𝐨𝐧
  isFunctor.isSetoidHom:map isFunctor:Free-𝐌𝐨𝐧 = {!!}
  isFunctor.functoriality-id isFunctor:Free-𝐌𝐨𝐧 = {!!}
  isFunctor.functoriality-◆ isFunctor:Free-𝐌𝐨𝐧 = {!!}

module _ {A : 𝒰 𝑖} {B : 𝒰 𝑗} where
  map-∍ : (f : A -> B) -> {as : Free-𝐌𝐨𝐧 A} {a : A} -> as ∍ a -> map-Free-𝐌𝐨𝐧 f as ∍ f a
  map-∍ f incl = incl
  map-∍ f (right-∍ x) = right-∍ (map-∍ f x)
  map-∍ f (left-∍ x) = left-∍ (map-∍ f x)


-- length of lists

module _ {A : 𝒰 𝑖} where
  人length : ∀(a : Free-𝐌𝐨𝐧 A) -> ℕ
  人length = rec-Free-𝐌𝐨𝐧 (const 1)


-----------------------------------------
-- we can decide whether an element is in a list

module _ {A : 𝒰 𝑖} {{_ : isDiscrete A}} where
  find-first-∍ : ∀ (xs : Free-𝐌𝐨𝐧 A) -> (x : A) -> isDecidable (xs ∍ x)
  find-first-∍ (incl y) x with x ≟-Str y
  ... | yes refl-≣ = just incl
  ... | no ¬p = left λ {incl → impossible (¬p refl-≣)}
  find-first-∍ (xs ⋆-Free-𝐌𝐨𝐧 ys) x with find-first-∍ xs x | find-first-∍ ys x
  ... | left ¬xs∍x | left ¬ys∍x = left λ { (left-∍ xs∍x) → ¬xs∍x xs∍x
                                         ; (right-∍ ys∍x) → ¬ys∍x ys∍x
                                         }
  ... | left ¬xs∍x | just ys∍x = just (right-∍ ys∍x)
  ... | just xs∍x | Y = right (left-∍ xs∍x)
  find-first-∍ ◌-Free-𝐌𝐨𝐧 x = left λ ()

-- //
