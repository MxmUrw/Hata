
module Verification.Experimental.Data.FiniteIndexed.Property.Merge where

open import Verification.Experimental.Conventions hiding (_⊔_)

open import Verification.Experimental.Set.Setoid.Definition
open import Verification.Experimental.Set.Set.Definition
open import Verification.Experimental.Set.Function.Injective
open import Verification.Experimental.Set.Discrete
open import Verification.Experimental.Set.Contradiction
-- open import Verification.Experimental.Set.Set.Instance.Category
open import Verification.Experimental.Category.Std.Category.Definition
open import Verification.Experimental.Category.Std.Functor.Definition
open import Verification.Experimental.Category.Std.Morphism.Iso
open import Verification.Experimental.Category.Std.Morphism.EpiMono
open import Verification.Experimental.Category.Std.Functor.Image
open import Verification.Experimental.Category.Std.Functor.Adjoint
open import Verification.Experimental.Category.Std.Category.Structured.SeparatingFamily

open import Verification.Experimental.Data.Universe.Definition
open import Verification.Experimental.Data.Universe.Everything
open import Verification.Experimental.Data.Universe.Instance.FiniteCoproductCategory
open import Verification.Experimental.Data.Universe.Instance.SeparatingFamily

open import Verification.Experimental.Data.Nat.Free
open import Verification.Experimental.Data.Indexed.Definition
open import Verification.Experimental.Data.Indexed.Xiix
open import Verification.Experimental.Data.Indexed.Instance.Monoid
open import Verification.Experimental.Data.Indexed.Instance.FiniteCoproductCategory
open import Verification.Experimental.Data.Indexed.Instance.SeparatingFamily

open import Verification.Experimental.Algebra.Monoid.Definition
open import Verification.Experimental.Algebra.Monoid.Free
open import Verification.Experimental.Algebra.Monoid.Free.Element

open import Verification.Experimental.Category.Std.Category.Subcategory.Full
open import Verification.Experimental.Category.Std.Limit.Specific.Coproduct.Definition
open import Verification.Experimental.Category.Std.Limit.Specific.Coproduct.Instance.Functor
open import Verification.Experimental.Category.Std.Limit.Specific.Coproduct.Preservation.Definition
open import Verification.Experimental.Category.Std.Category.Subcategory.Full.Construction.Coproduct

open import Verification.Experimental.Data.FiniteIndexed.Definition

private
  lem-0 : ∀{A : 𝒰 𝑖} -> (f g : ¬ A) -> f ≣ g
  lem-0 f g = ≡→≡-Str (funExt λ x → impossible (f x))

module _ {A : 𝒰 𝑖} where
  data _≠-∍_ : ∀{as : 人List A} {a b : A} (la : as ∍ a) (lb : as ∍ b) -> 𝒰 𝑖 where
    ≠-∍:bySort : ∀{x a b la lb} -> ¬ a ≣ b -> _≠-∍_ {incl x} {a} {b} (la) (lb)
    ≠-∍:left  : ∀{as bs : 人List A} -> {a b : A} -> {la : as ∍ a} {lb : as ∍ b} -> la ≠-∍ lb -> left-∍ {b = bs} la ≠-∍ left-∍ lb
    ≠-∍:right : ∀{as bs : 人List A} -> {a b : A} -> {la : as ∍ a} {lb : as ∍ b} -> la ≠-∍ lb -> right-∍ {a = bs} la ≠-∍ right-∍ lb
    ≠-∍:left-right : ∀{as bs : 人List A} -> {a b : A} -> {la : as ∍ a} {lb : bs ∍ b} -> left-∍ la ≠-∍ right-∍ lb
    ≠-∍:right-left : ∀{as bs : 人List A} -> {a b : A} -> {la : bs ∍ a} {lb : as ∍ b} -> right-∍ la ≠-∍ left-∍ lb

  -- TODO: change this to consist of two paths, the second dependent on the first
  data _=-∍_ : ∀{as : 人List A} {a b : A} (la : as ∍ a) (lb : as ∍ b) -> 𝒰 𝑖 where
    refl-=-∍ : ∀{as} {a : A} {la : as ∍ a} -> la =-∍ la

  cancel-injective-=-∍-right-∍ : ∀{as bs : 人List A} {a b : A} {la : as ∍ a} {lb : as ∍ b} -> (right-∍ {a = bs} la =-∍ right-∍ {a = bs} lb) -> la =-∍ lb
  cancel-injective-=-∍-right-∍ refl-=-∍ = refl-=-∍

  cancel-injective-=-∍-left-∍ : ∀{as bs : 人List A} {a b : A} {la : as ∍ a} {lb : as ∍ b} -> (left-∍ {b = bs} la =-∍ left-∍ {b = bs} lb) -> la =-∍ lb
  cancel-injective-=-∍-left-∍ refl-=-∍ = refl-=-∍


  isProp:≠-∍ : ∀{as : 人List A} {a b : A} -> {la : as ∍ a} {lb : as ∍ b} -> (p q : la ≠-∍ lb) -> p ≣ q
  isProp:≠-∍ (≠-∍:bySort x) (≠-∍:bySort x₁) = cong-Str ≠-∍:bySort (lem-0 _ _)
  isProp:≠-∍ (≠-∍:left p) (≠-∍:left q) = cong-Str ≠-∍:left (isProp:≠-∍ p q)
  isProp:≠-∍ (≠-∍:right p) (≠-∍:right q) = cong-Str ≠-∍:right (isProp:≠-∍ p q)
  isProp:≠-∍ ≠-∍:left-right ≠-∍:left-right = refl-≣
  isProp:≠-∍ ≠-∍:right-left ≠-∍:right-left = refl-≣

  -- cong-=-∍-right : ∀{as bs : 人List A} {a b : A} {la : as ∍ a} {lb : as ∍ b} -> la =-∍ lb -> right-∍ {a = bs} la =-∍ right-∍ {a = bs} lb
  -- cong-=-∍-right (refl-=-∍) = refl-=-∍

  =-∍→≣ : ∀{as : 人List A} {a b : A} {la : as ∍ a} {lb : as ∍ b} -> (la =-∍ lb) -> a ≣ b
  =-∍→≣ refl-=-∍ = refl-≣

  transport⁻¹-=-∍ : ∀{as : 人List A} {a b : A} {la : as ∍ a} {lb : as ∍ b} -> (P : A -> 𝒰 𝑗) -> (la =-∍ lb) -> P b -> P a
  transport⁻¹-=-∍ P p x = transport-Str (cong-Str P (sym-≣ (=-∍→≣ p))) x

  private
    skip-∍ : ∀{as : 人List A} {a : A} {la : as ∍ a} -> (la ≠-∍ la) -> ⊥-𝒰 {ℓ₀}
    skip-∍ (≠-∍:bySort x) = impossible (x refl-≣)
    skip-∍ (≠-∍:left p) = skip-∍ p
    skip-∍ (≠-∍:right p) = skip-∍ p

    compare-∍ : ∀{as : 人List A} {a b : A} {la : as ∍ a} {lb : as ∍ b} -> (la =-∍ lb) ×-𝒰 (la ≠-∍ lb) -> ⊥-𝒰 {ℓ₀}
    compare-∍ (refl-=-∍ , q) = skip-∍ q

  instance
    isContradiction:≠-∍ : ∀{as : 人List A} {a : A} {la : as ∍ a} -> isContradiction (la ≠-∍ la)
    isContradiction:≠-∍ = contradiction skip-∍

  instance
    isContradiction:=-∍,≠-∍ : ∀{as : 人List A} {a b : A} {la : as ∍ a} {lb : as ∍ b} -> isContradiction ((la =-∍ lb) ×-𝒰 (la ≠-∍ lb))
    isContradiction:=-∍,≠-∍ = contradiction compare-∍

  -- private
  --   lem-001 : ∀{as : 人List A} {a b : A} {la : as ∍ a} {lb : as ∍ b} -> (p0 : a ≣ b) -> (p : la =-∍ lb) -> p ≣ transport-Str (cong-Str (λ ξ -> as ∍ ξ) p0) refl-=-∍
  --   lem-001 = ?


module _ {A : 𝒰 𝑖} {{_ : isDiscrete A}} {{_ : isSet-Str A}} where

  transport⁻¹-=-∍-refl : ∀{as : 人List A} {a : A} {la : as ∍ a} -> (P : A -> 𝒰 𝑗) -> (p : la =-∍ la) -> (x : P a) -> transport⁻¹-=-∍ P p x ≣ x
  transport⁻¹-=-∍-refl P p x =
    let P0 : StrId (transport-Str (cong-Str P (sym-≣ (refl-≣))) x) x
        P0 = refl-≣

        P1 : StrId (transport-Str (cong-Str P (sym-≣ (=-∍→≣ p))) x) x
        P1 = transport-Str (cong-Str (λ ξ -> StrId (transport-Str (cong-Str P (sym-≣ (ξ))) x) x) (isset-Str refl-≣ (=-∍→≣ p))) P0
    in P1

  -- we want to show this by deconstructing an =-∍ statement into two path statements
  isProp-=-∍ : ∀{as : 人List A} {a : A} {b : A} {la : as ∍ a} {lb : as ∍ b} -> (p q : la =-∍ lb) -> p ≣ q
  isProp-=-∍ = {!!}

  -- isProp-=-∍ refl-=-∍ q = {!!}
  --   where
  --     lem-1 : {a : A} {b : A} {la : as ∍ a} {lb : as ∍ b} -> (p : a ≣ b) -> (q : la =-∍ lb) -> q ≣ transport-Str (cong (λ ξ -> ))


  _\\_ : (as : 人List A) -> {a : A} -> (as ∍ a) -> 人List A
  incl x \\ incl = ◌
  (as ⋆-⧜ bs) \\ right-∍ x = as ⋆ (bs \\ x)
  (as ⋆-⧜ bs) \\ left-∍ x = (as \\ x) ⋆ bs

  _\\'_ : (as : 𝐅𝐢𝐧𝐈𝐱 A) -> {a : A} -> (⟨ as ⟩ ∍ a) -> 𝐅𝐢𝐧𝐈𝐱 A
  _\\'_ as x = incl (⟨ as ⟩ \\ x)

  ι-\\ : ∀{as : 人List A} -> {a : A} -> (x : as ∍ a) -> 𝑒𝑙 (as \\ x) ⟶ 𝑒𝑙 as
  ι-\\ (right-∍ x) p (right-∍ y) = right-∍ (ι-\\ x p y)
  ι-\\ (right-∍ x) p (left-∍ y) = left-∍ y
  ι-\\ (left-∍ x) p (right-∍ y) = right-∍ y
  ι-\\ (left-∍ x) p (left-∍ y) = left-∍ (ι-\\ x p y)

  single-∍ : ∀{as : 人List A} -> {a : A} -> (x : as ∍ a) -> 𝑒𝑙 (incl a) ⟶ 𝑒𝑙 as
  single-∍ x i incl = x


  -- private
  --   skip-∍ : ∀{as : 人List A} {a b : A} -> (la : as ∍ a) -> (¬ a ≣ b) -> as ∍ b -> (as \\ la) ∍ b
  --   skip-∍ incl a≠b incl = impossible (a≠b refl-≣)
  --   skip-∍ (right-∍ la) a≠b (right-∍ lb) = right-∍ (skip-∍ la a≠b lb)
  --   skip-∍ (left-∍ la) a≠b (right-∍ lb) = right-∍ lb
  --   skip-∍ (right-∍ la) a≠b (left-∍ lb) = left-∍ lb
  --   skip-∍ (left-∍ la) a≠b (left-∍ lb) = left-∍ (skip-∍ la a≠b lb)

  --   compare-∍-0 : ∀{a b : A} -> (p : a ≣ b) -> (la : incl b ∍ a) -> la ≣ (transport-Str (cong-Str (λ ξ -> incl ξ ∍ a) p) incl)
  --   compare-∍-0 p incl = {!!}

  --   compare-∍ : ∀{as : 人List A} {a : A} -> (la lb : as ∍ a) -> (¬ la ≣ lb) -> (as \\ la) ∍ a
  --   compare-∍ incl lb a≠b = impossible (a≠b (sym-≣ (compare-∍-0 refl-≣ lb)))
  --   compare-∍ (right-∍ la) (right-∍ lb) a≠b = right-∍ (compare-∍ la lb (λ p -> a≠b (cong-Str right-∍ p)))
  --   compare-∍ (right-∍ la) (left-∍ lb) a≠b = left-∍ lb
  --   compare-∍ (left-∍ la) (right-∍ lb) a≠b = right-∍ lb
  --   compare-∍ (left-∍ la) (left-∍ lb) a≠b = left-∍ ((compare-∍ la lb (λ p -> a≠b (cong-Str left-∍ p))))

  skip-∍ : ∀{as : 人List A} {a b : A} -> (la : as ∍ a) -> (lb : as ∍ b) -> (la ≠-∍ lb) -> (as \\ lb) ∍ a
  skip-∍ incl incl (≠-∍:bySort x) = impossible (x refl-≣)
  skip-∍ (right-∍ la) (right-∍ lb) (≠-∍:right p) = right-∍ (skip-∍ la lb p)
  skip-∍ (right-∍ la) (left-∍ lb) ≠-∍:right-left = right-∍ la
  skip-∍ (left-∍ la) (right-∍ lb) ≠-∍:left-right = left-∍ la
  skip-∍ (left-∍ la) (left-∍ lb) (≠-∍:left p) = left-∍ (skip-∍ la lb p)

  compare-∍ : ∀{as : 人List A} {a b : A} -> (la : as ∍ a) -> (lb : as ∍ b) -> (la ≠-∍ lb) +-𝒰 (la =-∍ lb)
  compare-∍ incl incl = right (refl-=-∍)
  compare-∍ (right-∍ la) (right-∍ lb) with compare-∍ la lb
  ... | left x = left (≠-∍:right x)
  ... | just (refl-=-∍) = right (refl-=-∍)
  compare-∍ (right-∍ la) (left-∍ lb) = left ≠-∍:right-left
  compare-∍ (left-∍ la) (right-∍ lb) = left ≠-∍:left-right
  compare-∍ (left-∍ la) (left-∍ lb) with compare-∍ la lb
  ... | left x = left (≠-∍:left x)
  ... | just refl-=-∍ = just refl-=-∍

  π-\\ : ∀{as : 𝐅𝐢𝐧𝐈𝐱 A} -> {a : A} -> (x : ⟨ as ⟩ ∍ a) -> (y : ⟨ as ⟩ ∍ a) -> (y ≠-∍ x) -> as ⟶ (as \\' x)
  ⟨ π-\\ x y y≠x ⟩ i q with compare-∍ q x
  ... | left q≠x = skip-∍ q x q≠x
  ... | just r =
    let rr = skip-∍ y x y≠x
    in transport⁻¹-=-∍ _ r rr
  -- ... | just refl-=-∍ = skip-∍ y x y≠x

  private
    -- lem-3 : ∀{as : 𝐅𝐢𝐧𝐈𝐱 A} {a b : A} -> {x : ⟨ as ⟩ ∍ a} -> {x' : ⟨ as ⟩ ∍ b} -> (x =-∍ x') -> {y : ⟨ as ⟩ ∍ a} -> (p : y ≠-∍ x) -> ⟨ π-\\ x y p ⟩ b x' ≣ skip-∍ y x p
    lem-3 : ∀{as : 𝐅𝐢𝐧𝐈𝐱 A} {a : A} -> {x : ⟨ as ⟩ ∍ a}  -> {y : ⟨ as ⟩ ∍ a} -> (p : y ≠-∍ x) -> ⟨ π-\\ x y p ⟩ a x ≣ skip-∍ y x p
    lem-3 {a = a} {x} {y} p with compare-∍ x x
    ... | left q = impossible q
    ... | just p = transport⁻¹-=-∍-refl _ _ _

    lem-4 : ∀{as : 𝐅𝐢𝐧𝐈𝐱 A} {a : A} -> {x : ⟨ as ⟩ ∍ a}  -> {y : ⟨ as ⟩ ∍ a} -> (p : y ≠-∍ x) -> ⟨ π-\\ x y p ⟩ a y ≣ skip-∍ y x p
    lem-4 {a = a} {x} {y} (y≠x) with compare-∍ y x
    ... | left x₁ = cong-Str (λ ξ -> skip-∍ y x ξ) (isProp:≠-∍ _ _)
    ... | just y=x = impossible (y=x , y≠x)

  π-\\-∼ : ∀{as : 𝐅𝐢𝐧𝐈𝐱 A} {a : A} -> {x : ⟨ as ⟩ ∍ a} -> {y : ⟨ as ⟩ ∍ a} -> (p : y ≠-∍ x) -> ⟨ π-\\ x y p ⟩ a x ≣ ⟨ π-\\ x y p ⟩ a y
  π-\\-∼ {a = a} {x} {y} p = lem-3 p ∙-≣ sym-≣ (lem-4 p)

  private
    lem-5 : ∀{as : 𝐅𝐢𝐧𝐈𝐱 A} {a : A} -> {x : ⟨ as ⟩ ∍ a} -> ∀{b : A} -> {z : ⟨ as ⟩ ∍ b} -> (p : z ≠-∍ x) -> ι-\\ x b (skip-∍ z x p) ≣ z
    lem-5 {x = incl} {z = incl} (≠-∍:bySort x) = impossible (x refl-≣)
    lem-5 {x = right-∍ x} {z = right-∍ y} (≠-∍:right p) = cong-Str right-∍ (lem-5 p)
    lem-5 {x = right-∍ x} {z = left-∍ y} ≠-∍:left-right = refl-≣
    lem-5 {x = left-∍ x} {z = right-∍ y} ≠-∍:right-left = refl-≣
    lem-5 {x = left-∍ x} {z = left-∍ y} (≠-∍:left p) = cong-Str left-∍ (lem-5 p)

    -- lem-6 : ∀{as : 𝐅𝐢𝐧𝐈𝐱 A} {a : A} -> {x : ⟨ as ⟩ ∍ a} -> ∀{b : A} -> {z : ⟨ as ⟩ ∍ b} -> (p : z ≠-∍ x) -> ι-\\ x b (skip-∍ z x p) ≣ z
    -- lem-6 = ?

  merge-embed : ∀{as : 𝐅𝐢𝐧𝐈𝐱 A} {a : A} -> {x : ⟨ as ⟩ ∍ a} -> {y : ⟨ as ⟩ ∍ a} -> (p : y ≠-∍ x) -> ∀{b : A} -> (z : ⟨ as ⟩ ∍ b) -> (ι-\\ x b (⟨ π-\\ x y p ⟩ b z) ≣ z) +-𝒰 (z =-∍ x)
  merge-embed {x = x} p z with compare-∍ z x
  ... | left p2 = left (lem-5 p2)
  ... | just p2 = right p2

  merge-single : ∀{as : 𝐅𝐢𝐧𝐈𝐱 A} {a : A} -> {x : ⟨ as ⟩ ∍ a} -> {y : ⟨ as ⟩ ∍ a} -> (p : y ≠-∍ x) -> (ι-\\ x a (⟨ π-\\ x y p ⟩ a x) ≣ y)
  merge-single {as} {a} {x = x} {y} p with compare-∍ x x
  ... | left x≠x = impossible x≠x
  ... | just p2 = P
    where

      P9 : StrId
            (ι-\\ x a
            (transport-Str
              (cong-Str (_∍_ (⟨ as ⟩ \\ x)) (refl-≣))
              (skip-∍ y x p)))
            y
      P9 = lem-5 p

      P : StrId
            (ι-\\ x a
            (transport-Str
              (cong-Str (_∍_ (⟨ as ⟩ \\ x)) (sym-≣ (=-∍→≣ p2)))
              (skip-∍ y x p)))
            y
      P = transport-Str (cong-Str (λ ξ ->
            StrId
              (ι-\\ x a
              (transport-Str
                (cong-Str (_∍_ (⟨ as ⟩ \\ x)) (ξ))
                (skip-∍ y x p)))
              y)
              (isset-Str _ _)) P9



    -- let X : (ι-\\ x a (transport⁻¹-=-∍ (_∍_ (FullSubcategory.⟨ as ⟩ \\ x)) p2 (skip-∍ y x p)))
    --   y
    --     X = (lem-5 p)
    -- in ?

  private
    lem-6 : ∀{as : 𝐅𝐢𝐧𝐈𝐱 A} {a : A} -> {x : ⟨ as ⟩ ∍ a} -> ∀{b : A} -> {z : (⟨ as ⟩ \\ x) ∍ b} -> (p : (ι-\\ x b z) ≠-∍ x) -> (skip-∍ (ι-\\ x b z) x p) ≣ z
    lem-6 {x = right-∍ x} {z = right-∍ z} (≠-∍:right p) = cong-Str right-∍ (lem-6 p)
    lem-6 {x = right-∍ x} {z = left-∍ z} ≠-∍:left-right = refl-≣
    lem-6 {x = left-∍ x} {z = right-∍ z} ≠-∍:right-left = refl-≣
    lem-6 {x = left-∍ x} {z = left-∍ z} (≠-∍:left p)    = cong-Str left-∍ (lem-6 p)

    lem-7 : ∀{as : 𝐅𝐢𝐧𝐈𝐱 A} {a : A} -> {x : ⟨ as ⟩ ∍ a} -> ∀{b : A} -> {z : (⟨ as ⟩ \\ x) ∍ b} -> (p : (ι-\\ x b z) =-∍ x) -> 𝟘-𝒰
    lem-7 {x = right-∍ x} {z = right-∍ z} p = lem-7 (cancel-injective-=-∍-right-∍ p)
    lem-7 {x = left-∍ x} {z = left-∍ z} p   = lem-7 (cancel-injective-=-∍-left-∍ p)


  embed-merge : ∀{as : 𝐅𝐢𝐧𝐈𝐱 A} {a : A} -> {x : ⟨ as ⟩ ∍ a} -> {y : ⟨ as ⟩ ∍ a} -> (p : y ≠-∍ x) -> ∀{b : A} -> ∀ z -> ((⟨ π-\\ x y p ⟩ b (ι-\\ x b z)) ≣ z)
  embed-merge {as} {a} {x} {y} p {b} z with compare-∍ (ι-\\ x b z) x in q
  ... | left q = lem-6 q
  ... | just r = impossible (lem-7 r)


  iso-\\ : ∀{as : 人List A} -> {a : A} -> (x : as ∍ a) -> 𝑒𝑙 as ⟶ 𝑒𝑙 ((as \\ x)) ⊔ 𝑒𝑙 (incl a)
  iso-\\ x i y with compare-∍ y x
  ... | left x≠y = left (skip-∍ y x x≠y)
  ... | just refl-=-∍ = right incl

  iso⁻¹-\\ : ∀{as : 人List A} -> {a : A} -> (x : as ∍ a) -> 𝑒𝑙 ((as \\ x)) ⊔ 𝑒𝑙 (incl a) ⟶ 𝑒𝑙 as
  iso⁻¹-\\ x = ⦗ ι-\\ x , single-∍ x ⦘






