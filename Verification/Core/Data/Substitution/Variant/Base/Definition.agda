
module Verification.Core.Data.Substitution.Variant.Base.Definition where

open import Verification.Core.Conventions hiding (_⊔_)

open import Verification.Core.Set.Setoid.Definition
open import Verification.Core.Set.Discrete
open import Verification.Core.Set.Set.Definition
open import Verification.Core.Set.Function.Injective
open import Verification.Core.Set.Setoid.Morphism
open import Verification.Core.Set.Setoid.Morphism.Property
open import Verification.Core.Set.Contradiction
open import Verification.Core.Set.Function.Property
open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Category.Std.Functor.Definition
open import Verification.Core.Category.Std.Morphism.Iso
open import Verification.Core.Category.Std.Morphism.EpiMono
-- open import Verification.Core.Category.Std.Functor.Image
-- open import Verification.Core.Category.Std.Functor.Adjoint
open import Verification.Core.Category.Std.Functor.Faithful
open import Verification.Core.Category.Std.Functor.Full
open import Verification.Core.Category.Std.Functor.EssentiallySurjective
open import Verification.Core.Category.Std.Category.Structured.SeparatingFamily

open import Verification.Core.Data.Universe.Definition
open import Verification.Core.Data.Universe.Instance.Category
open import Verification.Core.Data.Universe.Instance.FiniteCoproductCategory
open import Verification.Core.Data.Universe.Instance.SeparatingFamily

-- open import Verification.Core.Data.List.Variant.Binary.Natural
open import Verification.Core.Data.Indexed.Definition
open import Verification.Core.Data.Indexed.Xiix
open import Verification.Core.Data.Indexed.Instance.Monoid
open import Verification.Core.Data.Indexed.Instance.FiniteCoproductCategory
open import Verification.Core.Data.Indexed.Instance.SeparatingFamily
open import Verification.Core.Data.FiniteIndexed.Definition

open import Verification.Core.Algebra.Monoid.Definition
open import Verification.Core.Data.List.Variant.Binary.Definition
open import Verification.Core.Data.List.Variant.Binary.Instance.Monoid
open import Verification.Core.Data.List.Variant.Binary.Element.Definition
open import Verification.Core.Data.List.Dependent.Variant.Binary.Definition

open import Verification.Core.Category.Std.Category.Subcategory.Full
open import Verification.Core.Category.Std.Limit.Specific.Coproduct.Definition
open import Verification.Core.Category.Std.Limit.Specific.Coproduct.Preservation.Definition
open import Verification.Core.Category.Std.Limit.Specific.Coproduct.Reflection.Definition
open import Verification.Core.Category.Std.Category.Subcategory.Full.Construction.Coproduct

open import Verification.Core.Category.Std.RelativeMonad.Definition
open import Verification.Core.Category.Std.RelativeMonad.KleisliCategory.Definition
open import Verification.Core.Category.Std.RelativeMonad.KleisliCategory.Instance.FiniteCoproductCategory
open import Verification.Core.Category.Std.RelativeMonad.KleisliCategory.Instance.IsoGetting
open import Verification.Core.Data.FiniteIndexed.Property.IsoGetting
open import Verification.Core.Category.Std.RelativeMonad.Finitary.Definition




module _ {A : 𝒰 𝑖} (R : ⋆List A -> A -> 𝒰 𝑖) where
  CtxHom : ⋆List A -> ⋆List A -> 𝒰 _
  CtxHom as bs = ⋆Listᴰ (R bs) as
  -- CtxHom as bs = ⋆List[ a ∈ as ] (R bs a)





-- [Hide]
module _ {I : 𝒰 𝑖} (T : FinitaryRelativeMonad I) where
  Substitution = RelativeKleisli T

  macro
    𝐒𝐮𝐛𝐬𝐭 : SomeStructure
    𝐒𝐮𝐛𝐬𝐭 = #structureOn (Substitution)


record InductiveSubstitution {I : 𝒰 𝑖} (T : FinitaryRelativeMonad I) : 𝒰 𝑖 where
  constructor incl
  field ⟨_⟩ : ⋆List I

{-# DISPLAY InductiveSubstitution.⟨_⟩ a = ⟨ a ⟩ #-}
open InductiveSubstitution {{...}} public

module _ {I : 𝒰 𝑖} (T : FinitaryRelativeMonad I) where
  macro ⧜𝐒𝐮𝐛𝐬𝐭 = #structureOn (InductiveSubstitution T)

module _ {I : 𝒰 𝑖} {T : FinitaryRelativeMonad I} where

  private
    T' : Functor _ _
    T' = ′ ⟨ T ⟩ ′

  ι-⧜𝐒𝐮𝐛𝐬𝐭ᵘ : ⧜𝐒𝐮𝐛𝐬𝐭 T -> 𝐒𝐮𝐛𝐬𝐭 T
  ι-⧜𝐒𝐮𝐛𝐬𝐭ᵘ (incl x) = incl (incl x)

  macro
    ι-⧜𝐒𝐮𝐛𝐬𝐭 = #structureOn ι-⧜𝐒𝐮𝐛𝐬𝐭ᵘ

  private
    RT : ⋆List I -> I -> 𝒰 _
    RT = (λ b a → ix (⟨ T ⟩ (incl b)) a)

  Hom-⧜𝐒𝐮𝐛𝐬𝐭 : (a b : ⧜𝐒𝐮𝐛𝐬𝐭 T) -> 𝒰 𝑖
  Hom-⧜𝐒𝐮𝐛𝐬𝐭 a b = CtxHom RT ⟨ a ⟩ ⟨ b ⟩

  record Hom-⧜𝐒𝐮𝐛𝐬𝐭' (a b : ⧜𝐒𝐮𝐛𝐬𝐭 T) : 𝒰 𝑖 where
    constructor ⧜subst
    field ⟨_⟩ : Hom-⧜𝐒𝐮𝐛𝐬𝐭 a b

  open Hom-⧜𝐒𝐮𝐛𝐬𝐭' public


  π₀-⋆-⧜𝐒𝐮𝐛𝐬𝐭-≣ : ∀{a b x : ⧜𝐒𝐮𝐛𝐬𝐭 T} -> {f g : Hom-⧜𝐒𝐮𝐛𝐬𝐭' a x} -> {h i : Hom-⧜𝐒𝐮𝐛𝐬𝐭' b x} -> StrId {A = Hom-⧜𝐒𝐮𝐛𝐬𝐭' (incl (⟨ a ⟩ ⋆ ⟨ b ⟩)) x} (⧜subst (⟨ f ⟩ ⋆-⧜ ⟨ h ⟩)) (⧜subst (⟨ g ⟩ ⋆-⧜ ⟨ i ⟩)) -> f ≣ g
  π₀-⋆-⧜𝐒𝐮𝐛𝐬𝐭-≣ refl-≣ = refl-≣

  π₁-⋆-⧜𝐒𝐮𝐛𝐬𝐭-≣ : ∀{a b x : ⧜𝐒𝐮𝐛𝐬𝐭 T} -> {f g : Hom-⧜𝐒𝐮𝐛𝐬𝐭' a x} -> {h i : Hom-⧜𝐒𝐮𝐛𝐬𝐭' b x} -> StrId {A = Hom-⧜𝐒𝐮𝐛𝐬𝐭' (incl (⟨ a ⟩ ⋆ ⟨ b ⟩)) x} (⧜subst (⟨ f ⟩ ⋆-⧜ ⟨ h ⟩)) (⧜subst (⟨ g ⟩ ⋆-⧜ ⟨ i ⟩)) -> h ≣ i
  π₁-⋆-⧜𝐒𝐮𝐛𝐬𝐭-≣ refl-≣ = refl-≣

  module _ {a b : ⧜𝐒𝐮𝐛𝐬𝐭 T} where

    instance
      isSetoid:Hom-⧜𝐒𝐮𝐛𝐬𝐭' : isSetoid (Hom-⧜𝐒𝐮𝐛𝐬𝐭' a b)
      isSetoid:Hom-⧜𝐒𝐮𝐛𝐬𝐭' = isSetoid:byId

  id-⧜𝐒𝐮𝐛𝐬𝐭' : ∀{a : ⧜𝐒𝐮𝐛𝐬𝐭 T} -> Hom-⧜𝐒𝐮𝐛𝐬𝐭 a a
  id-⧜𝐒𝐮𝐛𝐬𝐭' = construct-CtxHom λ a x → repure a x

  -- private
  sub-⧜𝐒𝐮𝐛𝐬𝐭 : ∀{b c} -> (Hom-⧜𝐒𝐮𝐛𝐬𝐭' b c) -> 𝑓𝑖𝑛 I (incl ⟨ b ⟩) ⟶ ⟨ T ⟩ (incl ⟨ c ⟩)
  sub-⧜𝐒𝐮𝐛𝐬𝐭 (⧜subst f) i x = destruct-CtxHom f i x

  subst-⧜𝐒𝐮𝐛𝐬𝐭 : ∀{b c} -> (Hom-⧜𝐒𝐮𝐛𝐬𝐭' (incl b) c) -> (⟨ T ⟩ (incl b)) ⟶ (⟨ T ⟩ (incl ⟨ c ⟩))
  subst-⧜𝐒𝐮𝐛𝐬𝐭 f = (reext (sub-⧜𝐒𝐮𝐛𝐬𝐭 f))

  _◆-⧜𝐒𝐮𝐛𝐬𝐭''_ : ∀{a b c : ⧜𝐒𝐮𝐛𝐬𝐭 T} -> (Hom-⧜𝐒𝐮𝐛𝐬𝐭 a b) -> (Hom-⧜𝐒𝐮𝐛𝐬𝐭 b c) -> Hom-⧜𝐒𝐮𝐛𝐬𝐭 a c
  _◆-⧜𝐒𝐮𝐛𝐬𝐭''_ f g = construct-CtxHom (destruct-CtxHom f ◆ reext (destruct-CtxHom g))

  _◆-⧜𝐒𝐮𝐛𝐬𝐭'_ : ∀{a b c : ⧜𝐒𝐮𝐛𝐬𝐭 T} -> (Hom-⧜𝐒𝐮𝐛𝐬𝐭 a b) -> (Hom-⧜𝐒𝐮𝐛𝐬𝐭' b c) -> Hom-⧜𝐒𝐮𝐛𝐬𝐭 a c
  _◆-⧜𝐒𝐮𝐛𝐬𝐭'_ f g = construct-CtxHom (destruct-CtxHom f ◆ subst-⧜𝐒𝐮𝐛𝐬𝐭 g)


  _◆-⧜𝐒𝐮𝐛𝐬𝐭_ : ∀{a b c : ⧜𝐒𝐮𝐛𝐬𝐭 T} -> (Hom-⧜𝐒𝐮𝐛𝐬𝐭' a b) -> (Hom-⧜𝐒𝐮𝐛𝐬𝐭' b c) -> Hom-⧜𝐒𝐮𝐛𝐬𝐭' a c
  _◆-⧜𝐒𝐮𝐛𝐬𝐭_ f g = ⧜subst $ ⟨ f ⟩ ◆-⧜𝐒𝐮𝐛𝐬𝐭' g

  id-⧜𝐒𝐮𝐛𝐬𝐭 : ∀{a : ⧜𝐒𝐮𝐛𝐬𝐭 T} -> Hom-⧜𝐒𝐮𝐛𝐬𝐭' a a
  id-⧜𝐒𝐮𝐛𝐬𝐭 = ⧜subst id-⧜𝐒𝐮𝐛𝐬𝐭'



  ----------------------------------------------------------
  -- the inclusion ι

  instance
    hasInclusion:⧜𝐒𝐮𝐛𝐬𝐭,𝐒𝐮𝐛𝐬𝐭 : hasInclusion (⧜𝐒𝐮𝐛𝐬𝐭 T) (𝐒𝐮𝐛𝐬𝐭 T)
    hasInclusion:⧜𝐒𝐮𝐛𝐬𝐭,𝐒𝐮𝐛𝐬𝐭 = inclusion ι-⧜𝐒𝐮𝐛𝐬𝐭

  -- it is a functor

  map-ι-⧜𝐒𝐮𝐛𝐬𝐭 : ∀{b c : ⧜𝐒𝐮𝐛𝐬𝐭 T} -> Hom-⧜𝐒𝐮𝐛𝐬𝐭' b c -> ι-⧜𝐒𝐮𝐛𝐬𝐭 b ⟶ ι-⧜𝐒𝐮𝐛𝐬𝐭 c
  map-ι-⧜𝐒𝐮𝐛𝐬𝐭 f = incl (sub-⧜𝐒𝐮𝐛𝐬𝐭 f)

  private
    lem-01 : ∀{b c : ⧜𝐒𝐮𝐛𝐬𝐭 T} -> {f g : Hom-⧜𝐒𝐮𝐛𝐬𝐭' b c} -> f ∼ g -> map-ι-⧜𝐒𝐮𝐛𝐬𝐭 f ∼ map-ι-⧜𝐒𝐮𝐛𝐬𝐭 g
    lem-01 refl-≣ = refl

    -- functoriality id
    lem-02 : ∀{a : ⧜𝐒𝐮𝐛𝐬𝐭 T} -> map-ι-⧜𝐒𝐮𝐛𝐬𝐭 (id-⧜𝐒𝐮𝐛𝐬𝐭 {a = a}) ∼ id
    lem-02 = incl (funExt⁻¹ (inv-l-◆-construct-⋆Listᴰ _))

    -- functoriality ◆
    lem-03 : ∀{a b c : ⧜𝐒𝐮𝐛𝐬𝐭 T} {f : Hom-⧜𝐒𝐮𝐛𝐬𝐭' a b} {g : Hom-⧜𝐒𝐮𝐛𝐬𝐭' b c} -> map-ι-⧜𝐒𝐮𝐛𝐬𝐭 (f ◆-⧜𝐒𝐮𝐛𝐬𝐭 g) ∼ map-ι-⧜𝐒𝐮𝐛𝐬𝐭 f ◆ map-ι-⧜𝐒𝐮𝐛𝐬𝐭 g
    lem-03 = incl (funExt⁻¹ (inv-l-◆-construct-⋆Listᴰ _))

  instance
    isSetoidHom:map-ι-⧜𝐒𝐮𝐛𝐬𝐭 : ∀{b c : 𝐒𝐮𝐛𝐬𝐭 T} -> isSetoidHom ′(Hom-⧜𝐒𝐮𝐛𝐬𝐭' (incl ⟨ ⟨ b ⟩ ⟩) (incl ⟨ ⟨ c ⟩ ⟩))′ (b ⟶ c) map-ι-⧜𝐒𝐮𝐛𝐬𝐭
    isSetoidHom:map-ι-⧜𝐒𝐮𝐛𝐬𝐭 = record { cong-∼ = lem-01 }

  private
    -- injectivity of map
    cancel-injective-map-ι-⧜𝐒𝐮𝐛𝐬𝐭 : ∀{a b : ⧜𝐒𝐮𝐛𝐬𝐭 T} -> ∀{f g : Hom-⧜𝐒𝐮𝐛𝐬𝐭' a b} -> map-ι-⧜𝐒𝐮𝐛𝐬𝐭 f ∼ map-ι-⧜𝐒𝐮𝐛𝐬𝐭 g -> f ∼ g
    cancel-injective-map-ι-⧜𝐒𝐮𝐛𝐬𝐭 {a} {b} {f} {g} (incl p) =
      let p' = funExt p

          p'' : ⟨ f ⟩ ≡ ⟨ g ⟩
          p'' = cancel-injective-𝒰 p'

          p''' : f ≡ g
          p''' = cong ⧜subst (p'')
      in ≡→≡-Str p'''

  instance
    isInjective:map-ι-⧜𝐒𝐮𝐛𝐬𝐭 : ∀{a b : ⧜𝐒𝐮𝐛𝐬𝐭 T} -> isInjective (map-ι-⧜𝐒𝐮𝐛𝐬𝐭 {a} {b})
    isInjective:map-ι-⧜𝐒𝐮𝐛𝐬𝐭 = record { cancel-injective = cancel-injective-map-ι-⧜𝐒𝐮𝐛𝐬𝐭 }

  surj-map-ι-⧜𝐒𝐮𝐛𝐬𝐭 : ∀{a b : ⧜𝐒𝐮𝐛𝐬𝐭 T} -> ι a ⟶ ι b -> Hom-⧜𝐒𝐮𝐛𝐬𝐭' a b
  surj-map-ι-⧜𝐒𝐮𝐛𝐬𝐭 f = ⧜subst (construct-⋆Listᴰ ⟨ f ⟩)

  instance
    isSetoidHom:surj-map-ι-⧜𝐒𝐮𝐛𝐬𝐭 : ∀{a b : ⧜𝐒𝐮𝐛𝐬𝐭 T} -> isSetoidHom (ι a ⟶ ι b) ′(Hom-⧜𝐒𝐮𝐛𝐬𝐭' a b)′ surj-map-ι-⧜𝐒𝐮𝐛𝐬𝐭
    isSetoidHom:surj-map-ι-⧜𝐒𝐮𝐛𝐬𝐭 = record { cong-∼ = λ {(incl p) → ≡→≡-Str (λ i -> ⧜subst (construct-⋆Listᴰ (funExt p i))) } }

  inv-surj-map-ι-⧜𝐒𝐮𝐛𝐬𝐭 : ∀{a b : ⧜𝐒𝐮𝐛𝐬𝐭 T} -> ∀{f : ι a ⟶ ι b} -> map-ι-⧜𝐒𝐮𝐛𝐬𝐭 (surj-map-ι-⧜𝐒𝐮𝐛𝐬𝐭 f) ∼ f
  inv-surj-map-ι-⧜𝐒𝐮𝐛𝐬𝐭 = incl (funExt⁻¹ (inv-l-◆-construct-⋆Listᴰ _))

  instance
    isSurjective:map-ι-⧜𝐒𝐮𝐛𝐬𝐭 : ∀{a b : ⧜𝐒𝐮𝐛𝐬𝐭 T} -> isSurjective (map-ι-⧜𝐒𝐮𝐛𝐬𝐭 {a} {b})
    isSurjective:map-ι-⧜𝐒𝐮𝐛𝐬𝐭 = surjective surj-map-ι-⧜𝐒𝐮𝐛𝐬𝐭 {{isSetoidHom:surj-map-ι-⧜𝐒𝐮𝐛𝐬𝐭}} inv-surj-map-ι-⧜𝐒𝐮𝐛𝐬𝐭

  abstract
    内id-⧜𝐒𝐮𝐛𝐬𝐭 : ∀{a : ⧜𝐒𝐮𝐛𝐬𝐭 T} -> Hom-⧜𝐒𝐮𝐛𝐬𝐭' a a
    内id-⧜𝐒𝐮𝐛𝐬𝐭 = id-⧜𝐒𝐮𝐛𝐬𝐭

    _内◆-⧜𝐒𝐮𝐛𝐬𝐭_ : ∀{a b c : ⧜𝐒𝐮𝐛𝐬𝐭 T} -> (Hom-⧜𝐒𝐮𝐛𝐬𝐭' a b) -> (Hom-⧜𝐒𝐮𝐛𝐬𝐭' b c) -> Hom-⧜𝐒𝐮𝐛𝐬𝐭' a c
    _内◆-⧜𝐒𝐮𝐛𝐬𝐭_ = _◆-⧜𝐒𝐮𝐛𝐬𝐭_

    lem-02-abstract : ∀{a : ⧜𝐒𝐮𝐛𝐬𝐭 T} -> map-ι-⧜𝐒𝐮𝐛𝐬𝐭 (内id-⧜𝐒𝐮𝐛𝐬𝐭 {a = a}) ∼ id
    lem-02-abstract = lem-02

    -- functoriality ◆
    lem-03-abstract : ∀{a b c : ⧜𝐒𝐮𝐛𝐬𝐭 T} {f : Hom-⧜𝐒𝐮𝐛𝐬𝐭' a b} {g : Hom-⧜𝐒𝐮𝐛𝐬𝐭' b c} -> map-ι-⧜𝐒𝐮𝐛𝐬𝐭 (f 内◆-⧜𝐒𝐮𝐛𝐬𝐭 g) ∼ map-ι-⧜𝐒𝐮𝐛𝐬𝐭 f ◆ map-ι-⧜𝐒𝐮𝐛𝐬𝐭 g
    lem-03-abstract {a} {b} {c} {f} {g} = lem-03 {a} {b} {c} {f} {g}

    {-# DISPLAY _内◆-⧜𝐒𝐮𝐛𝐬𝐭_ f g = f ◆ g #-}
    {-# DISPLAY 内id-⧜𝐒𝐮𝐛𝐬𝐭 = id #-}

    abstract-◆-⧜𝐒𝐮𝐛𝐬𝐭 : ∀{a b c : ⧜𝐒𝐮𝐛𝐬𝐭 T} {f : Hom-⧜𝐒𝐮𝐛𝐬𝐭' a b} {g : Hom-⧜𝐒𝐮𝐛𝐬𝐭' b c} -> (f ◆-⧜𝐒𝐮𝐛𝐬𝐭 g) ∼ (f 内◆-⧜𝐒𝐮𝐛𝐬𝐭 g)
    abstract-◆-⧜𝐒𝐮𝐛𝐬𝐭 = refl-≣

    abstract-id-⧜𝐒𝐮𝐛𝐬𝐭 : ∀{a : ⧜𝐒𝐮𝐛𝐬𝐭 T} -> id-⧜𝐒𝐮𝐛𝐬𝐭 ∼ 内id-⧜𝐒𝐮𝐛𝐬𝐭 {a = a}
    abstract-id-⧜𝐒𝐮𝐛𝐬𝐭 = refl-≣

    ≀abstract≀-◆-⧜𝐒𝐮𝐛𝐬𝐭 : ∀{a b c : ⧜𝐒𝐮𝐛𝐬𝐭 T} {f f' : Hom-⧜𝐒𝐮𝐛𝐬𝐭' a b} {g g' : Hom-⧜𝐒𝐮𝐛𝐬𝐭' b c} -> (f ◆-⧜𝐒𝐮𝐛𝐬𝐭 g) ∼ (f' ◆-⧜𝐒𝐮𝐛𝐬𝐭 g') -> (f 内◆-⧜𝐒𝐮𝐛𝐬𝐭 g) ∼ (f' 内◆-⧜𝐒𝐮𝐛𝐬𝐭 g')
    ≀abstract≀-◆-⧜𝐒𝐮𝐛𝐬𝐭 p = p

    ≀abstract⁻¹≀-◆-⧜𝐒𝐮𝐛𝐬𝐭 : ∀{a b c : ⧜𝐒𝐮𝐛𝐬𝐭 T} {f f' : Hom-⧜𝐒𝐮𝐛𝐬𝐭' a b} {g g' : Hom-⧜𝐒𝐮𝐛𝐬𝐭' b c} -> (f 内◆-⧜𝐒𝐮𝐛𝐬𝐭 g) ∼ (f' 内◆-⧜𝐒𝐮𝐛𝐬𝐭 g') -> (f ◆-⧜𝐒𝐮𝐛𝐬𝐭 g) ∼ (f' ◆-⧜𝐒𝐮𝐛𝐬𝐭 g')
    ≀abstract⁻¹≀-◆-⧜𝐒𝐮𝐛𝐬𝐭 p = p


  instance
    isCategory:⧜𝐒𝐮𝐛𝐬𝐭 : isCategory {𝑖 , 𝑖} (⧜𝐒𝐮𝐛𝐬𝐭 T)
    isCategory:⧜𝐒𝐮𝐛𝐬𝐭 = isCategory:byFaithful
      Hom-⧜𝐒𝐮𝐛𝐬𝐭'
      内id-⧜𝐒𝐮𝐛𝐬𝐭
      _内◆-⧜𝐒𝐮𝐛𝐬𝐭_
      ι-⧜𝐒𝐮𝐛𝐬𝐭
      map-ι-⧜𝐒𝐮𝐛𝐬𝐭
      (λ {a} {b} {c} {f} {g} -> lem-03-abstract {a} {b} {c} {f} {g})
      lem-02-abstract


  ----------------------------------------------------------
  -- the inclusion ι


  instance
    isFunctor:ι-⧜𝐒𝐮𝐛𝐬𝐭 : isFunctor (⧜𝐒𝐮𝐛𝐬𝐭 T) (𝐒𝐮𝐛𝐬𝐭 T) ι
    isFunctor.map isFunctor:ι-⧜𝐒𝐮𝐛𝐬𝐭 = map-ι-⧜𝐒𝐮𝐛𝐬𝐭
    isFunctor.isSetoidHom:map isFunctor:ι-⧜𝐒𝐮𝐛𝐬𝐭 = it
    isFunctor.functoriality-id isFunctor:ι-⧜𝐒𝐮𝐛𝐬𝐭 = lem-02-abstract
    isFunctor.functoriality-◆ isFunctor:ι-⧜𝐒𝐮𝐛𝐬𝐭 {a} {b} {c} {f} {g} = lem-03-abstract {a} {b} {c} {f} {g}


  instance
    isFaithful:ι-⧜𝐒𝐮𝐛𝐬𝐭 : isFaithful (ι-⧜𝐒𝐮𝐛𝐬𝐭)
    isFaithful.isInjective:map isFaithful:ι-⧜𝐒𝐮𝐛𝐬𝐭 = isInjective:map-ι-⧜𝐒𝐮𝐛𝐬𝐭


  instance
    isFull:ι-⧜𝐒𝐮𝐛𝐬𝐭 : isFull (ι-⧜𝐒𝐮𝐛𝐬𝐭)
    isFull:ι-⧜𝐒𝐮𝐛𝐬𝐭 = record {}

  eso-⧜𝐒𝐮𝐛𝐬𝐭 : (𝐒𝐮𝐛𝐬𝐭 T) -> ⧜𝐒𝐮𝐛𝐬𝐭 T
  eso-⧜𝐒𝐮𝐛𝐬𝐭 (incl (incl x)) = incl x

  instance
    isEssentiallySurjective:ι-⧜𝐒𝐮𝐛𝐬𝐭 : isEssentiallySurjective (ι-⧜𝐒𝐮𝐛𝐬𝐭)
    isEssentiallySurjective.eso isEssentiallySurjective:ι-⧜𝐒𝐮𝐛𝐬𝐭 = eso-⧜𝐒𝐮𝐛𝐬𝐭
    isEssentiallySurjective.inv-eso isEssentiallySurjective:ι-⧜𝐒𝐮𝐛𝐬𝐭 = refl-≅


  instance
    hasInitial:⧜𝐒𝐮𝐛𝐬𝐭 : hasInitial (⧜𝐒𝐮𝐛𝐬𝐭 T)
    hasInitial:⧜𝐒𝐮𝐛𝐬𝐭 = hasInitial:byFFEso

  ⊥-⧜𝐒𝐮𝐛𝐬𝐭 : ⧜𝐒𝐮𝐛𝐬𝐭 T
  ⊥-⧜𝐒𝐮𝐛𝐬𝐭 = incl ◌

  instance
    isInitial:⊥-⧜𝐒𝐮𝐛𝐬𝐭 : isInitial ⊥-⧜𝐒𝐮𝐛𝐬𝐭
    isInitial:⊥-⧜𝐒𝐮𝐛𝐬𝐭 = isInitial:⊥

  -- abstract
  instance
    hasCoproducts:⧜𝐒𝐮𝐛𝐬𝐭 : hasCoproducts (⧜𝐒𝐮𝐛𝐬𝐭 T)
    hasCoproducts:⧜𝐒𝐮𝐛𝐬𝐭 = hasCoproducts:byFFEso

  instance
    hasFiniteCoproducts:⧜𝐒𝐮𝐛𝐬𝐭 : hasFiniteCoproducts (⧜𝐒𝐮𝐛𝐬𝐭 T)
    hasFiniteCoproducts:⧜𝐒𝐮𝐛𝐬𝐭 = hasFiniteCoproducts:byFFEso

  module _ {a b : ⧜𝐒𝐮𝐛𝐬𝐭 T} where
    instance
      isCoproduct:⊔-⧜𝐒𝐮𝐛𝐬𝐭 : isCoproduct a b (a ⊔ b)
      isCoproduct:⊔-⧜𝐒𝐮𝐛𝐬𝐭 = isCoproduct:⊔



-----------------------------------------
-- Iso getting
--
  module _ {{_ : isDiscrete I}} where
    hasIsoGetting:⧜𝐒𝐮𝐛𝐬𝐭 : hasIsoGetting (⧜𝐒𝐮𝐛𝐬𝐭 T)
    hasIsoGetting:⧜𝐒𝐮𝐛𝐬𝐭 = hasIsoGetting:byFFEso hasIsoGetting:RelativeKleisli

-- //

-----------------------------------------
-- isomorphism between this category and the
-- non-inductively defined one
  open import Verification.Core.Category.Std.Functor.Equivalence
  instance
    isIso-𝐂𝐚𝐭:ι-⧜𝐒𝐮𝐛𝐬𝐭 : isIso-𝐂𝐚𝐭 ι-⧜𝐒𝐮𝐛𝐬𝐭
    isIso-𝐂𝐚𝐭:ι-⧜𝐒𝐮𝐛𝐬𝐭 = isIso-𝐂𝐚𝐭:byFFEso

-----------------------------------------
-- finite coproduct generated
--
  open import Verification.Core.Category.Std.Category.Structured.FiniteCoproductGenerated
  instance
    isFiniteCoproductGenerated:⧜𝐒𝐮𝐛𝐬𝐭 : {{_ : isFiniteCoproductGenerated (𝐒𝐮𝐛𝐬𝐭 T)}}
                                        -> isFiniteCoproductGenerated (⧜𝐒𝐮𝐛𝐬𝐭 T)
    isFiniteCoproductGenerated:⧜𝐒𝐮𝐛𝐬𝐭 = isFiniteCoproductGenerated:by≅-𝐂𝐚𝐭 (sym-≅-𝐂𝐚𝐭 ι-⧜𝐒𝐮𝐛𝐬𝐭)

