
module Verification.Experimental.Data.Substitution.Definition where

open import Verification.Experimental.Conventions hiding (_⊔_)

open import Verification.Experimental.Set.Setoid.Definition
open import Verification.Experimental.Set.Set.Definition
open import Verification.Experimental.Set.Setoid.Morphism
open import Verification.Experimental.Set.Contradiction
-- open import Verification.Experimental.Set.Set.Instance.Category
open import Verification.Experimental.Category.Std.Category.Definition
open import Verification.Experimental.Category.Std.Functor.Definition
open import Verification.Experimental.Category.Std.Morphism.Iso
open import Verification.Experimental.Category.Std.Morphism.EpiMono
open import Verification.Experimental.Category.Std.Functor.Image
open import Verification.Experimental.Category.Std.Functor.Adjoint
open import Verification.Experimental.Category.Std.Functor.Faithful
open import Verification.Experimental.Category.Std.Functor.Full
open import Verification.Experimental.Category.Std.Functor.EssentiallySurjective
open import Verification.Experimental.Category.Std.Category.Structured.SeparatingFamily

open import Verification.Experimental.Data.Universe.Definition
open import Verification.Experimental.Data.Universe.Everything
open import Verification.Experimental.Data.Universe.Instance.FiniteCoproductCategory
open import Verification.Experimental.Data.Universe.Instance.SeparatingFamily

open import Verification.Experimental.Data.Indexed.Definition
open import Verification.Experimental.Data.Indexed.Xiix
open import Verification.Experimental.Data.Indexed.Instance.Monoid
open import Verification.Experimental.Data.Indexed.Instance.FiniteCoproductCategory
open import Verification.Experimental.Data.Indexed.Instance.SeparatingFamily
open import Verification.Experimental.Data.FiniteIndexed.Definition

open import Verification.Experimental.Algebra.Monoid.Definition
open import Verification.Experimental.Algebra.Monoid.Free
open import Verification.Experimental.Algebra.Monoid.Free.Element

open import Verification.Experimental.Category.Std.Category.Subcategory.Full
open import Verification.Experimental.Category.Std.Limit.Specific.Coproduct.Definition
open import Verification.Experimental.Category.Std.Limit.Specific.Coproduct.Preservation.Definition
open import Verification.Experimental.Category.Std.Limit.Specific.Coproduct.Reflection.Definition
open import Verification.Experimental.Category.Std.Category.Subcategory.Full.Construction.Coproduct

open import Verification.Experimental.Category.Std.RelativeMonad.Definition
open import Verification.Experimental.Category.Std.RelativeMonad.KleisliCategory.Definition
open import Verification.Experimental.Category.Std.RelativeMonad.KleisliCategory.Instance.FiniteCoproductCategory



module _ (I : 𝒰 𝑖) where
  private
    fin : 𝐅𝐢𝐧𝐈𝐱 I -> (𝐈𝐱 I (𝐔𝐧𝐢𝐯 𝑖))
    fin = 𝑓𝑢𝑙𝑙 _ 𝑒𝑙
  macro
    𝑓𝑖𝑛 = #structureOn fin

-- module _ {I : 𝒰 𝑖} (T : Functor (𝐅𝐢𝐧𝐈𝐱 I) (𝐈𝐱 I (𝐔𝐧𝐢𝐯 𝑖))) {{_ : isRelativeMonad (𝑓𝑢𝑙𝑙 _ _) T}} where

module _ {I : 𝒰 𝑖} (T : RelativeMonad (𝑓𝑖𝑛 I)) where
  Substitution = RelativeKleisli T

  macro
    𝐒𝐮𝐛𝐬𝐭 : SomeStructure
    𝐒𝐮𝐛𝐬𝐭 = #structureOn (Substitution)

record InductiveSubstitution {I : 𝒰 𝑖} (T : RelativeMonad (𝑓𝑖𝑛 I)) : 𝒰 𝑖 where
  constructor incl
  field ⟨_⟩ : Free-𝐌𝐨𝐧 I

open InductiveSubstitution {{...}} public

module _ {I : 𝒰 𝑖} (T : RelativeMonad (𝑓𝑖𝑛 I)) where
  macro ⧜𝐒𝐮𝐛𝐬𝐭 = #structureOn (InductiveSubstitution T)

module _ {I : 𝒰 𝑖} {T : RelativeMonad (𝑓𝑖𝑛 I)} where
  private
    T' : Functor _ _
    T' = ′ ⟨ T ⟩ ′

  ι-⧜𝐒𝐮𝐛𝐬𝐭ᵘ : ⧜𝐒𝐮𝐛𝐬𝐭 T -> 𝐒𝐮𝐛𝐬𝐭 T
  ι-⧜𝐒𝐮𝐛𝐬𝐭ᵘ (incl x) = incl (incl x)

  macro
    ι-⧜𝐒𝐮𝐛𝐬𝐭 = #structureOn ι-⧜𝐒𝐮𝐛𝐬𝐭ᵘ


  data Hom-⧜𝐒𝐮𝐛𝐬𝐭 : (a b : ⧜𝐒𝐮𝐛𝐬𝐭 T) -> 𝒰 𝑖 where
    ◌-⧜ : ∀{b} -> Hom-⧜𝐒𝐮𝐛𝐬𝐭 (incl ◌) b
    incl : ∀{a b} -> ix (⟨ T ⟩ (incl b)) a -> Hom-⧜𝐒𝐮𝐛𝐬𝐭 (incl (incl a)) (incl b)
    _⋆-⧜_ : ∀{a b x} -> Hom-⧜𝐒𝐮𝐛𝐬𝐭 a x -> Hom-⧜𝐒𝐮𝐛𝐬𝐭 b x -> Hom-⧜𝐒𝐮𝐛𝐬𝐭 (incl (⟨ a ⟩ ⋆ ⟨ b ⟩)) x
    -- ι-l-⧜ : ∀{a b x : ⧜𝐒𝐮𝐛𝐬𝐭 T} -> Hom-⧜𝐒𝐮𝐛𝐬𝐭 x a -> Hom-⧜𝐒𝐮𝐛𝐬𝐭 x (incl (⟨ a ⟩ ⋆ ⟨ b ⟩))
    -- ι-r-⧜ : ∀{a b x : ⧜𝐒𝐮𝐛𝐬𝐭 T} -> Hom-⧜𝐒𝐮𝐛𝐬𝐭 x b -> Hom-⧜𝐒𝐮𝐛𝐬𝐭 x (incl (⟨ a ⟩ ⋆ ⟨ b ⟩))

  private
    ι-l-⧜ : ∀{a b x : ⧜𝐒𝐮𝐛𝐬𝐭 T} -> Hom-⧜𝐒𝐮𝐛𝐬𝐭 x a -> Hom-⧜𝐒𝐮𝐛𝐬𝐭 x (incl (⟨ a ⟩ ⋆ ⟨ b ⟩))
    ι-l-⧜ ◌-⧜           = ◌-⧜
    ι-l-⧜ (incl x)      = incl (map {{of T'}} ι₀ _ x)
    ι-l-⧜ (f ⋆-⧜ g)     = ι-l-⧜ f ⋆-⧜ ι-l-⧜ g

    ι-r-⧜ : ∀{a b x : ⧜𝐒𝐮𝐛𝐬𝐭 T} -> Hom-⧜𝐒𝐮𝐛𝐬𝐭 x b -> Hom-⧜𝐒𝐮𝐛𝐬𝐭 x (incl (⟨ a ⟩ ⋆ ⟨ b ⟩))
    ι-r-⧜ ◌-⧜           = ◌-⧜
    ι-r-⧜ (incl x)      = incl (map {{of T'}} ι₁ _ x)
    ι-r-⧜ (f ⋆-⧜ g)     = ι-r-⧜ f ⋆-⧜ ι-r-⧜ g

  incl-Hom-⧜𝐒𝐮𝐛𝐬𝐭 : ∀{a b} -> ix (⟨ T ⟩ (incl b)) a -> Hom-⧜𝐒𝐮𝐛𝐬𝐭 (incl (incl a)) (incl b)
  incl-Hom-⧜𝐒𝐮𝐛𝐬𝐭 = incl

  cancel-injective-incl-Hom-⧜𝐒𝐮𝐛𝐬𝐭 : ∀{a b} -> {f g : ix (⟨ T ⟩ (incl b)) a} -> incl-Hom-⧜𝐒𝐮𝐛𝐬𝐭 f ≣ incl-Hom-⧜𝐒𝐮𝐛𝐬𝐭 g -> f ≣ g
  cancel-injective-incl-Hom-⧜𝐒𝐮𝐛𝐬𝐭 refl-≣ = refl-≣

  module _ {a b : ⧜𝐒𝐮𝐛𝐬𝐭 T} where
    instance
      isSetoid:Hom-⧜𝐒𝐮𝐛𝐬𝐭 : isSetoid (Hom-⧜𝐒𝐮𝐛𝐬𝐭 a b)
      isSetoid:Hom-⧜𝐒𝐮𝐛𝐬𝐭 = isSetoid:byStrId

  id-⧜𝐒𝐮𝐛𝐬𝐭 : ∀{a : ⧜𝐒𝐮𝐛𝐬𝐭 T} -> Hom-⧜𝐒𝐮𝐛𝐬𝐭 a a
  id-⧜𝐒𝐮𝐛𝐬𝐭 {incl (incl x)}    = incl (repure x incl)
  id-⧜𝐒𝐮𝐛𝐬𝐭 {incl (a ⋆-⧜ b)}  = (ι-l-⧜ id-⧜𝐒𝐮𝐛𝐬𝐭) ⋆-⧜ (ι-r-⧜ id-⧜𝐒𝐮𝐛𝐬𝐭)
  id-⧜𝐒𝐮𝐛𝐬𝐭 {incl ◌-⧜}        = ◌-⧜

  private
    sub : ∀{b c} -> (Hom-⧜𝐒𝐮𝐛𝐬𝐭 b c) -> 𝑓𝑖𝑛 I (incl ⟨ b ⟩) ⟶ ⟨ T ⟩ (incl ⟨ c ⟩)
    sub ◌-⧜        = λ {i ()}
    sub (incl x)   = λ {i incl → x}
    sub (f ⋆-⧜ g)  = ⟨ preserves-⊔ ⟩ ◆ ⦗ sub f , sub g ⦘

  subst-⧜𝐒𝐮𝐛𝐬𝐭 : ∀{a b c} -> (Hom-⧜𝐒𝐮𝐛𝐬𝐭 (incl b) c) -> (x : ix (⟨ T ⟩ (incl b)) a) -> ix (⟨ T ⟩ (incl ⟨ c ⟩)) a
  subst-⧜𝐒𝐮𝐛𝐬𝐭 f x = (reext (sub f) _ x)

  _◆-⧜𝐒𝐮𝐛𝐬𝐭_ : ∀{a b c : ⧜𝐒𝐮𝐛𝐬𝐭 T} -> (Hom-⧜𝐒𝐮𝐛𝐬𝐭 a b) -> (Hom-⧜𝐒𝐮𝐛𝐬𝐭 b c) -> Hom-⧜𝐒𝐮𝐛𝐬𝐭 a c
  ◌-⧜ ◆-⧜𝐒𝐮𝐛𝐬𝐭 g = ◌-⧜
  incl x ◆-⧜𝐒𝐮𝐛𝐬𝐭 g = incl (subst-⧜𝐒𝐮𝐛𝐬𝐭 g x)
  (f ⋆-⧜ g) ◆-⧜𝐒𝐮𝐛𝐬𝐭 h = (f ◆-⧜𝐒𝐮𝐛𝐬𝐭 h) ⋆-⧜ (g ◆-⧜𝐒𝐮𝐛𝐬𝐭 h)


  instance
    isCategory:⧜𝐒𝐮𝐛𝐬𝐭 : isCategory (⧜𝐒𝐮𝐛𝐬𝐭 T)
    isCategory.Hom isCategory:⧜𝐒𝐮𝐛𝐬𝐭          = Hom-⧜𝐒𝐮𝐛𝐬𝐭
    isCategory.isSetoid:Hom isCategory:⧜𝐒𝐮𝐛𝐬𝐭 = it
    isCategory.id isCategory:⧜𝐒𝐮𝐛𝐬𝐭           = id-⧜𝐒𝐮𝐛𝐬𝐭
    isCategory._◆_ isCategory:⧜𝐒𝐮𝐛𝐬𝐭          = _◆-⧜𝐒𝐮𝐛𝐬𝐭_
    isCategory.unit-l-◆ isCategory:⧜𝐒𝐮𝐛𝐬𝐭     = {!!}
    isCategory.unit-r-◆ isCategory:⧜𝐒𝐮𝐛𝐬𝐭     = {!!}
    isCategory.unit-2-◆ isCategory:⧜𝐒𝐮𝐛𝐬𝐭     = {!!}
    isCategory.assoc-l-◆ isCategory:⧜𝐒𝐮𝐛𝐬𝐭    = {!!}
    isCategory.assoc-r-◆ isCategory:⧜𝐒𝐮𝐛𝐬𝐭    = {!!}
    isCategory._◈_ isCategory:⧜𝐒𝐮𝐛𝐬𝐭          = {!!}


  ----------------------------------------------------------
  -- the inclusion ι : ⧜𝐒𝐮𝐛𝐬𝐭 T -> 𝐒𝐮𝐛𝐬𝐭 T

  instance
    hasInclusion:⧜𝐒𝐮𝐛𝐬𝐭,𝐒𝐮𝐛𝐬𝐭 : hasInclusion (⧜𝐒𝐮𝐛𝐬𝐭 T) (𝐒𝐮𝐛𝐬𝐭 T)
    hasInclusion:⧜𝐒𝐮𝐛𝐬𝐭,𝐒𝐮𝐛𝐬𝐭 = inclusion ι-⧜𝐒𝐮𝐛𝐬𝐭

  -- it is a functor

  map-ι-⧜𝐒𝐮𝐛𝐬𝐭 : ∀{b c : ⧜𝐒𝐮𝐛𝐬𝐭 T} -> b ⟶ c -> ι-⧜𝐒𝐮𝐛𝐬𝐭 b ⟶ ι-⧜𝐒𝐮𝐛𝐬𝐭 c
  map-ι-⧜𝐒𝐮𝐛𝐬𝐭 f = incl (sub f)

  instance
    isSetoidHom:map-ι-⧜𝐒𝐮𝐛𝐬𝐭 : ∀{b c : 𝐒𝐮𝐛𝐬𝐭 T} -> isSetoidHom ′(Hom-⧜𝐒𝐮𝐛𝐬𝐭 (incl ⟨ ⟨ b ⟩ ⟩) (incl ⟨ ⟨ c ⟩ ⟩))′ ′(b ⟶ c)′ map-ι-⧜𝐒𝐮𝐛𝐬𝐭
    isSetoidHom:map-ι-⧜𝐒𝐮𝐛𝐬𝐭 = {!!}

  instance
    isFunctor:ι-⧜𝐒𝐮𝐛𝐬𝐭 : isFunctor (⧜𝐒𝐮𝐛𝐬𝐭 T) (𝐒𝐮𝐛𝐬𝐭 T) ι
    isFunctor.map isFunctor:ι-⧜𝐒𝐮𝐛𝐬𝐭 = map-ι-⧜𝐒𝐮𝐛𝐬𝐭
    isFunctor.isSetoidHom:map isFunctor:ι-⧜𝐒𝐮𝐛𝐬𝐭 = it
    isFunctor.functoriality-id isFunctor:ι-⧜𝐒𝐮𝐛𝐬𝐭 = {!!}
    isFunctor.functoriality-◆ isFunctor:ι-⧜𝐒𝐮𝐛𝐬𝐭 = {!!}


  -- which is full, faithful, eso
  cancel-injective-map-ι-⧜𝐒𝐮𝐛𝐬𝐭 : ∀{a b : ⧜𝐒𝐮𝐛𝐬𝐭 T} -> ∀{f g : a ⟶ b} -> map-ι-⧜𝐒𝐮𝐛𝐬𝐭 f ∼ map-ι-⧜𝐒𝐮𝐛𝐬𝐭 g -> f ∼ g
  cancel-injective-map-ι-⧜𝐒𝐮𝐛𝐬𝐭 = {!!}

  instance
    isInjective:map-ι-⧜𝐒𝐮𝐛𝐬𝐭 : ∀{a b : ⧜𝐒𝐮𝐛𝐬𝐭 T} -> isInjective (map-ι-⧜𝐒𝐮𝐛𝐬𝐭 {a} {b})
    isInjective:map-ι-⧜𝐒𝐮𝐛𝐬𝐭 = record { cancel-injective = cancel-injective-map-ι-⧜𝐒𝐮𝐛𝐬𝐭 }

  instance
    isFaithful:ι-⧜𝐒𝐮𝐛𝐬𝐭 : isFaithful (ι-⧜𝐒𝐮𝐛𝐬𝐭)
    isFaithful.isInjective:map isFaithful:ι-⧜𝐒𝐮𝐛𝐬𝐭 = isInjective:map-ι-⧜𝐒𝐮𝐛𝐬𝐭
    -- λ {a} {b} -> isInjective:map-ι-⧜𝐒𝐮𝐛𝐬𝐭 {a} {b}

  surj-map-ι-⧜𝐒𝐮𝐛𝐬𝐭 : ∀{a b : ⧜𝐒𝐮𝐛𝐬𝐭 T} -> ι a ⟶ ι b -> a ⟶ b
  surj-map-ι-⧜𝐒𝐮𝐛𝐬𝐭 {incl (incl x)}     (f) = incl (⟨ f ⟩ _ incl)
  surj-map-ι-⧜𝐒𝐮𝐛𝐬𝐭 {incl (a ⋆-⧜ a₁)}  (f) = surj-map-ι-⧜𝐒𝐮𝐛𝐬𝐭 (ι₀ ◆ f) ⋆-⧜ surj-map-ι-⧜𝐒𝐮𝐛𝐬𝐭 (ι₁ ◆ f)
  surj-map-ι-⧜𝐒𝐮𝐛𝐬𝐭 {incl ◌-⧜}         (f) = ◌-⧜

  inv-surj-map-ι-⧜𝐒𝐮𝐛𝐬𝐭 : ∀{a b : ⧜𝐒𝐮𝐛𝐬𝐭 T} -> ∀{f : ι a ⟶ ι b} -> map (surj-map-ι-⧜𝐒𝐮𝐛𝐬𝐭 f) ∼ f
  inv-surj-map-ι-⧜𝐒𝐮𝐛𝐬𝐭 = {!!}

  instance
    isSurjective:map-ι-⧜𝐒𝐮𝐛𝐬𝐭 : ∀{a b : ⧜𝐒𝐮𝐛𝐬𝐭 T} -> isSurjective (map-ι-⧜𝐒𝐮𝐛𝐬𝐭 {a} {b})
    isSurjective:map-ι-⧜𝐒𝐮𝐛𝐬𝐭 = surjective surj-map-ι-⧜𝐒𝐮𝐛𝐬𝐭 inv-surj-map-ι-⧜𝐒𝐮𝐛𝐬𝐭

  instance
    isFull:ι-⧜𝐒𝐮𝐛𝐬𝐭 : isFull (ι-⧜𝐒𝐮𝐛𝐬𝐭)
    isFull:ι-⧜𝐒𝐮𝐛𝐬𝐭 = {!!}

  eso-⧜𝐒𝐮𝐛𝐬𝐭 : (𝐒𝐮𝐛𝐬𝐭 T) -> ⧜𝐒𝐮𝐛𝐬𝐭 T
  eso-⧜𝐒𝐮𝐛𝐬𝐭 (incl (incl x)) = incl x

  instance
    isEssentiallySurjective:ι-⧜𝐒𝐮𝐛𝐬𝐭 : isEssentiallySurjective (ι-⧜𝐒𝐮𝐛𝐬𝐭)
    isEssentiallySurjective.eso isEssentiallySurjective:ι-⧜𝐒𝐮𝐛𝐬𝐭 = eso-⧜𝐒𝐮𝐛𝐬𝐭
    isEssentiallySurjective.inv-eso isEssentiallySurjective:ι-⧜𝐒𝐮𝐛𝐬𝐭 = refl-≅

  instance
    hasInitial:⧜𝐒𝐮𝐛𝐬𝐭 : hasInitial (⧜𝐒𝐮𝐛𝐬𝐭 T)
    hasInitial:⧜𝐒𝐮𝐛𝐬𝐭 = hasInitial:byFFEso



-- module _ {I : 𝒰 𝑖} where
--   Hom-⧜𝐅𝐢𝐧𝐈𝐱 : ⧜𝐅𝐢𝐧𝐈𝐱 -> ⧜𝐅𝐢𝐧𝐈𝐱 -> 𝒰 𝑖

