
module Verification.Core.Data.Substitution.Variant.Normal.Definition where

open import Verification.Core.Conventions hiding (_⊔_)

open import Verification.Core.Set.Setoid.Definition
open import Verification.Core.Set.Discrete
open import Verification.Core.Set.Set.Definition
open import Verification.Core.Set.Function.Injective
open import Verification.Core.Set.Setoid.Morphism
open import Verification.Core.Set.Setoid.Morphism.Property
open import Verification.Core.Set.Contradiction
open import Verification.Core.Set.Function.Property
-- open import Verification.Core.Set.Set.Instance.Category
open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Category.Std.Functor.Definition
open import Verification.Core.Category.Std.Morphism.Iso
open import Verification.Core.Category.Std.Morphism.EpiMono
open import Verification.Core.Category.Std.Functor.Image
open import Verification.Core.Category.Std.Functor.Adjoint
open import Verification.Core.Category.Std.Functor.Faithful
open import Verification.Core.Category.Std.Functor.Full
open import Verification.Core.Category.Std.Functor.EssentiallySurjective
open import Verification.Core.Category.Std.Category.Structured.SeparatingFamily

open import Verification.Core.Data.Universe.Definition
open import Verification.Core.Data.Universe.Definition
open import Verification.Core.Data.Universe.Instance.Category
open import Verification.Core.Data.Universe.Instance.FiniteCoproductCategory
open import Verification.Core.Data.Universe.Instance.SeparatingFamily

open import Verification.Core.Data.List.Variant.Binary.Natural
open import Verification.Core.Data.Indexed.Definition
open import Verification.Core.Data.Indexed.Xiix
open import Verification.Core.Data.Indexed.Instance.Monoid
open import Verification.Core.Data.Indexed.Instance.FiniteCoproductCategory
open import Verification.Core.Data.Indexed.Instance.SeparatingFamily
open import Verification.Core.Data.FiniteIndexed.Definition

open import Verification.Core.Algebra.Monoid.Definition
open import Verification.Core.Algebra.Monoid.Free
open import Verification.Core.Data.List.Variant.Binary.Element.Definition
open import Verification.Core.Data.List.Dependent.Variant.Binary.Definition
open import Verification.Core.Data.List.Dependent.Variant.Unary.Definition
open import Verification.Core.Data.List.Variant.Binary.Element.Definition
open import Verification.Core.Data.List.Variant.Binary.Element.Instance.Functor
open import Verification.Core.Data.List.Variant.Binary.Element.As.Indexed
open import Verification.Core.Data.List.Variant.Binary.Element.Properties
open import Verification.Core.Data.List.Variant.Binary.Natural
open import Verification.Core.Data.List.Variant.Binary.Misc
open import Verification.Core.Data.List.Variant.Binary.Definition
open import Verification.Core.Data.List.Variant.Binary.Instance.Monoid
open import Verification.Core.Data.List.Variant.Binary.Instance.Setoid
open import Verification.Core.Data.List.VariantTranslation.Definition

open import Verification.Core.Category.Std.Category.Subcategory.Full
open import Verification.Core.Category.Std.Limit.Specific.Coproduct.Definition
open import Verification.Core.Category.Std.Limit.Specific.Coproduct.Preservation.Definition
open import Verification.Core.Category.Std.Limit.Specific.Coproduct.Reflection.Definition
open import Verification.Core.Category.Std.Category.Subcategory.Full.Construction.Coproduct

open import Verification.Core.Category.Std.RelativeMonad.Definition
open import Verification.Core.Category.Std.RelativeMonad.Finitary.Definition
open import Verification.Core.Category.Std.RelativeMonad.KleisliCategory.Definition
open import Verification.Core.Category.Std.RelativeMonad.KleisliCategory.Instance.FiniteCoproductCategory
open import Verification.Core.Category.Std.RelativeMonad.KleisliCategory.Instance.IsoGetting
open import Verification.Core.Data.FiniteIndexed.Property.IsoGetting

open import Verification.Core.Data.Substitution.Variant.Base.Definition


module _ {A : 𝒰 𝑖} {B : A -> 𝒰 𝑗} where


  -- construct-Listᴰ : ∀{as : List A} -> (∀ a -> as ∍♮ a -> B a) -> Listᴰ B as
  -- construct-Listᴰ {[]} f = []
  -- construct-Listᴰ {x ∷ as} f = (f x incl) ∷ (construct-Listᴰ (λ a x -> f a (skip x)))

  -- destruct-Listᴰ : ∀{as : List A} -> Listᴰ B as -> (∀ a -> as ∍♮ a -> B a)
  -- destruct-Listᴰ {[]} [] a ()
  -- destruct-Listᴰ {x ∷ as} (b ∷ xs) .x incl = b
  -- destruct-Listᴰ {x ∷ as} (b ∷ xs) a (skip p) = destruct-Listᴰ xs a p

  construct-Listᴰ-人Listᴰ : ∀{as : List A} -> ⋆Listᴰ B (ι as) -> Listᴰ B as
  construct-Listᴰ-人Listᴰ {[]} xs = []
  construct-Listᴰ-人Listᴰ {x ∷ as} (incl x₁ ⋆-⧜ xs₁) = x₁ ∷ (construct-Listᴰ-人Listᴰ xs₁)

  destruct-Listᴰ-人Listᴰ : ∀{as : List A} -> Listᴰ B as -> ⋆Listᴰ B (ι as)
  destruct-Listᴰ-人Listᴰ {[]} xs = ◌-⧜
  destruct-Listᴰ-人Listᴰ {x ∷ as} (b ∷ xs) = incl b ⋆-⧜ destruct-Listᴰ-人Listᴰ xs

  inv-l-◆-construct-Listᴰ : ∀{as : List A} -> (r : ⋆Listᴰ B (ι as)) -> destruct-Listᴰ-人Listᴰ (construct-Listᴰ-人Listᴰ r) ≡ r
  inv-l-◆-construct-Listᴰ {[]} ◌-⧜ = λ i → ◌-⧜
  inv-l-◆-construct-Listᴰ {x ∷ as} (incl x₁ ⋆-⧜ xs₁) = λ i → (incl x₁) ⋆-⧜ (inv-l-◆-construct-Listᴰ xs₁ i)

  inv-r-◆-construct-Listᴰ : ∀{as : List A} -> (f : Listᴰ B as) -> construct-Listᴰ-人Listᴰ (destruct-Listᴰ-人Listᴰ f) ≡ f
  inv-r-◆-construct-Listᴰ {[]} [] = λ i → []
  inv-r-◆-construct-Listᴰ {x ∷ as} (b ∷ xs) = λ i → b ∷ inv-r-◆-construct-Listᴰ xs i



module _ {A : 𝒰 𝑖}  where
  ListᴰHom : (B : List A -> A -> 𝒰 𝑗) -> List A -> List A -> 𝒰 _
  ListᴰHom B as bs = Listᴰ (B bs) as


-- list based inductive substitutions

record NormalInductiveSubstitution {I : 𝒰 𝑖} (T : RelativeMonad (𝑓𝑖𝑛 I)) : 𝒰 𝑖 where
  constructor incl
  field ⟨_⟩ : List I

{-# DISPLAY NormalInductiveSubstitution.⟨_⟩ a = ⟨ a ⟩ #-}
open NormalInductiveSubstitution {{...}} public

module _ {I : 𝒰 𝑖} (T : RelativeMonad (𝑓𝑖𝑛 I)) where
  macro ♮𝐒𝐮𝐛𝐬𝐭 = #structureOn (NormalInductiveSubstitution T)


module _ {I : 𝒰 𝑖} {T' : RelativeMonad (𝑓𝑖𝑛 I)} where

  private macro T = #structureOn ⟨ T' ⟩

  private
    RT : List I -> I -> 𝒰 _
    RT = (λ b a → ix (T (incl (ι b))) a)

  Hom-♮𝐒𝐮𝐛𝐬𝐭' : (a b : ♮𝐒𝐮𝐛𝐬𝐭 T) -> 𝒰 𝑖
  Hom-♮𝐒𝐮𝐛𝐬𝐭' a b = ListᴰHom RT ⟨ a ⟩ ⟨ b ⟩

  record Hom-♮𝐒𝐮𝐛𝐬𝐭 (a b : ♮𝐒𝐮𝐛𝐬𝐭 T) : 𝒰 𝑖 where
    constructor ♮subst
    field ⟨_⟩ : Hom-♮𝐒𝐮𝐛𝐬𝐭' a b

  open Hom-♮𝐒𝐮𝐛𝐬𝐭 public

  ι-♮𝐒𝐮𝐛𝐬𝐭ᵘ : (♮𝐒𝐮𝐛𝐬𝐭 T) -> (⧜𝐒𝐮𝐛𝐬𝐭 T)
  ι-♮𝐒𝐮𝐛𝐬𝐭ᵘ = (λ a -> incl (ι ⟨ a ⟩))

  macro ι-♮𝐒𝐮𝐛𝐬𝐭 = #structureOn ι-♮𝐒𝐮𝐛𝐬𝐭ᵘ

  instance
    hasInclusion:♮𝐒𝐮𝐛𝐬𝐭,⧜𝐒𝐮𝐛𝐬𝐭 : hasInclusion (♮𝐒𝐮𝐛𝐬𝐭 T) (⧜𝐒𝐮𝐛𝐬𝐭 T)
    hasInclusion:♮𝐒𝐮𝐛𝐬𝐭,⧜𝐒𝐮𝐛𝐬𝐭 = inclusion ι-♮𝐒𝐮𝐛𝐬𝐭

  module _ {a b : ♮𝐒𝐮𝐛𝐬𝐭 T} where
    instance
      isSetoid:Hom-♮𝐒𝐮𝐛𝐬𝐭 : isSetoid (Hom-♮𝐒𝐮𝐛𝐬𝐭 a b)
      isSetoid:Hom-♮𝐒𝐮𝐛𝐬𝐭 = isSetoid:byId


    map-ι-♮𝐒𝐮𝐛𝐬𝐭 : (f : Hom-♮𝐒𝐮𝐛𝐬𝐭 a b) -> (ι a ⟶ ι b)
    map-ι-♮𝐒𝐮𝐛𝐬𝐭 (♮subst f) = ⧜subst (destruct-Listᴰ-人Listᴰ f)

  instance
    isSetoidHom:map-ι-♮𝐒𝐮𝐛𝐬𝐭 : {a b : NormalInductiveSubstitution ′ ⟨ T' ⟩ ′} →
                                  isSetoidHom ′ Hom-♮𝐒𝐮𝐛𝐬𝐭 a b ′
                                  (incl (ι ⟨ a ⟩) ⟶ incl (ι ⟨ b ⟩))
                                  map-ι-♮𝐒𝐮𝐛𝐬𝐭
    isSetoidHom:map-ι-♮𝐒𝐮𝐛𝐬𝐭 = record { cong-∼ = λ {refl-≣ → refl-≣} }

    isInjective:map-ι-♮𝐒𝐮𝐛𝐬𝐭 : {a b : NormalInductiveSubstitution ′ ⟨ T' ⟩ ′} → isInjective (map-ι-♮𝐒𝐮𝐛𝐬𝐭 {a = a} {b = b})
    isInjective:map-ι-♮𝐒𝐮𝐛𝐬𝐭 {a} {b} = record { cancel-injective = λ p -> cong-Str ♮subst (lem-1 (lem-2 p)) }
      where
        lem-2 : ∀{a b} -> ∀{f g : Hom-⧜𝐒𝐮𝐛𝐬𝐭 {T = T} a b} -> ⧜subst {T = T} f ≣ ⧜subst g -> f ≣ g
        lem-2 refl-≣ = refl-≣


        lem-1 : ∀{a b} -> ∀{f g : Hom-♮𝐒𝐮𝐛𝐬𝐭' a b} -> destruct-Listᴰ-人Listᴰ f ≣ destruct-Listᴰ-人Listᴰ g -> f ≣ g
        lem-1 {f = []} {[]} p = refl-≣
        lem-1 {f = b ∷ f} {b₁ ∷ g} p with §-⋆Listᴰ.prop-1 p
        ... | refl-≣ , Y with lem-1 Y
        ... | refl-≣ = refl-≣


  surj-map-ι-♮𝐒𝐮𝐛𝐬𝐭 : ∀{a b : ♮𝐒𝐮𝐛𝐬𝐭 T} -> ι a ⟶ ι b -> Hom-♮𝐒𝐮𝐛𝐬𝐭 a b
  surj-map-ι-♮𝐒𝐮𝐛𝐬𝐭 f = ♮subst (construct-Listᴰ-人Listᴰ ⟨ f ⟩)

  inv-surj-map-ι-♮𝐒𝐮𝐛𝐬𝐭 : ∀{a b : ♮𝐒𝐮𝐛𝐬𝐭 T} -> ∀{f : ι a ⟶ ι b} -> map-ι-♮𝐒𝐮𝐛𝐬𝐭 (surj-map-ι-♮𝐒𝐮𝐛𝐬𝐭 f) ∼ f
  inv-surj-map-ι-♮𝐒𝐮𝐛𝐬𝐭 = cong-Str ⧜subst (≡→≡-Str (inv-l-◆-construct-Listᴰ _))

  instance
    isSurjective:map-ι-♮𝐒𝐮𝐛𝐬𝐭 : ∀{a b : ♮𝐒𝐮𝐛𝐬𝐭 T} -> isSurjective (map-ι-♮𝐒𝐮𝐛𝐬𝐭 {a} {b})
    isSurjective:map-ι-♮𝐒𝐮𝐛𝐬𝐭 = surjective surj-map-ι-♮𝐒𝐮𝐛𝐬𝐭 {{?}} inv-surj-map-ι-♮𝐒𝐮𝐛𝐬𝐭



  id-♮𝐒𝐮𝐛𝐬𝐭 : ∀{a} -> Hom-♮𝐒𝐮𝐛𝐬𝐭 a a
  id-♮𝐒𝐮𝐛𝐬𝐭 = ♮subst (construct-Listᴰ-人Listᴰ (id-⧜𝐒𝐮𝐛𝐬𝐭' {T = T}))

  _◆-♮𝐒𝐮𝐛𝐬𝐭_ : ∀{a b c} -> Hom-♮𝐒𝐮𝐛𝐬𝐭 a b -> Hom-♮𝐒𝐮𝐛𝐬𝐭 b c -> Hom-♮𝐒𝐮𝐛𝐬𝐭 a c
  ♮subst f ◆-♮𝐒𝐮𝐛𝐬𝐭 ♮subst g = ♮subst (construct-Listᴰ-人Listᴰ (_◆-⧜𝐒𝐮𝐛𝐬𝐭''_ {T = T} (destruct-Listᴰ-人Listᴰ f) (destruct-Listᴰ-人Listᴰ g)))

  private
    lem-1 : {a b c : NormalInductiveSubstitution ′ ⟨ T' ⟩ ′}
            {f : Hom-♮𝐒𝐮𝐛𝐬𝐭 a b} {g : Hom-♮𝐒𝐮𝐛𝐬𝐭 b c} →
            (it isSetoid.∼ map-ι-♮𝐒𝐮𝐛𝐬𝐭 (f ◆-♮𝐒𝐮𝐛𝐬𝐭 g))
            (map-ι-♮𝐒𝐮𝐛𝐬𝐭 f ◆ map-ι-♮𝐒𝐮𝐛𝐬𝐭 g)
    lem-1 {a}{b}{c}{f}{g} = ≡→≡-Str (cong ⧜subst ( inv-l-◆-construct-Listᴰ _)) ∙-≣ abstract-◆-⧜𝐒𝐮𝐛𝐬𝐭

    lem-2 : {a : NormalInductiveSubstitution ′ ⟨ T' ⟩ ′} → (it isSetoid.∼ map-ι-♮𝐒𝐮𝐛𝐬𝐭 (id-♮𝐒𝐮𝐛𝐬𝐭 {a = a})) id
    lem-2 = ≡→≡-Str (cong ⧜subst (inv-l-◆-construct-Listᴰ _)) ∙-≣ abstract-id-⧜𝐒𝐮𝐛𝐬𝐭


  abstract
    instance
      isCategory:♮𝐒𝐮𝐛𝐬𝐭 : isCategory {𝑖 , 𝑖} (♮𝐒𝐮𝐛𝐬𝐭 T)
      isCategory:♮𝐒𝐮𝐛𝐬𝐭 = isCategory:byFaithful Hom-♮𝐒𝐮𝐛𝐬𝐭 id-♮𝐒𝐮𝐛𝐬𝐭 _◆-♮𝐒𝐮𝐛𝐬𝐭_ ι map-ι-♮𝐒𝐮𝐛𝐬𝐭 lem-1 lem-2

    instance
      isFunctor:ι-♮𝐒𝐮𝐛𝐬𝐭 : isFunctor (♮𝐒𝐮𝐛𝐬𝐭 T) (⧜𝐒𝐮𝐛𝐬𝐭 T) ι
      isFunctor:ι-♮𝐒𝐮𝐛𝐬𝐭 = functor map-ι-♮𝐒𝐮𝐛𝐬𝐭 lem-2 lem-1

    instance
      isFaithful:ι-♮𝐒𝐮𝐛𝐬𝐭 : isFaithful (ι-♮𝐒𝐮𝐛𝐬𝐭)
      isFaithful.isInjective:map isFaithful:ι-♮𝐒𝐮𝐛𝐬𝐭 = isInjective:map-ι-♮𝐒𝐮𝐛𝐬𝐭

    instance
      isFull:ι-♮𝐒𝐮𝐛𝐬𝐭 : isFull (ι-♮𝐒𝐮𝐛𝐬𝐭)
      isFull:ι-♮𝐒𝐮𝐛𝐬𝐭 = record {}

    eso-♮𝐒𝐮𝐛𝐬𝐭 : (⧜𝐒𝐮𝐛𝐬𝐭 T) -> ♮𝐒𝐮𝐛𝐬𝐭 T
    eso-♮𝐒𝐮𝐛𝐬𝐭 (incl x) = incl (♮ x)

    instance
      isEssentiallySurjective:ι-♮𝐒𝐮𝐛𝐬𝐭 : isEssentiallySurjective (ι-♮𝐒𝐮𝐛𝐬𝐭)
      isEssentiallySurjective.eso isEssentiallySurjective:ι-♮𝐒𝐮𝐛𝐬𝐭 = eso-♮𝐒𝐮𝐛𝐬𝐭
      isEssentiallySurjective.inv-eso isEssentiallySurjective:ι-♮𝐒𝐮𝐛𝐬𝐭 {d} = lem-01
        where
          -- NOTE: we currently need a `module _ where` here, because
          -- otherwise the `abstract` outside is applied to
          -- every line individually, and then does not see
          -- that the type and term definitions belong together
          module _ where
            -- in 𝐈𝐱
            lem-04 : 𝑒𝑙 (ι (♮ ⟨ d ⟩)) ≅ 𝑒𝑙 ⟨ d ⟩
            lem-04 = cong-∼ surj-♮-⋆List

            d'' : 𝐅𝐢𝐧𝐈𝐱 I
            d'' = incl ⟨ d ⟩

            -- in 𝐅𝐢𝐧𝐈𝐱
            lem-03 : (incl (ι (♮ ⟨ d ⟩))) ≅ d''
            lem-03 = cong⁻¹-≅ lem-04

            d' : 𝐒𝐮𝐛𝐬𝐭 T
            d' = incl (incl ⟨ d ⟩)

            -- in 𝐑𝐞𝐊𝐥𝐬 T = 𝐒𝐮𝐛𝐬𝐭
            lem-02 : incl (incl (ι (♮ ⟨ d ⟩))) ≅ d'
            lem-02 = cong-≅ lem-03

            -- in ⧜𝐒𝐮𝐛𝐬𝐭
            lem-01 : incl (ι (♮ ⟨ d ⟩)) ≅ d
            lem-01 = cong⁻¹-≅ lem-02


  abstract
    instance
      hasInitial:♮𝐒𝐮𝐛𝐬𝐭 : hasInitial (♮𝐒𝐮𝐛𝐬𝐭 T)
      hasInitial:♮𝐒𝐮𝐛𝐬𝐭 = hasInitial:byFFEso

    instance
      hasCoproducts:♮𝐒𝐮𝐛𝐬𝐭 : hasCoproducts (♮𝐒𝐮𝐛𝐬𝐭 T)
      hasCoproducts:♮𝐒𝐮𝐛𝐬𝐭 = hasCoproducts:byFFEso

    instance
      hasFiniteCoproducts:♮𝐒𝐮𝐛𝐬𝐭 : hasFiniteCoproducts (♮𝐒𝐮𝐛𝐬𝐭 T)
      hasFiniteCoproducts:♮𝐒𝐮𝐛𝐬𝐭 = hasFiniteCoproducts:byFFEso

    module _ {a b : ♮𝐒𝐮𝐛𝐬𝐭 T} where
      instance
        isCoproduct:⊔-♮𝐒𝐮𝐛𝐬𝐭 : isCoproduct a b (a ⊔ b)
        isCoproduct:⊔-♮𝐒𝐮𝐛𝐬𝐭 = isCoproduct:⊔



    -----------------------------------------
    -- "Iso getting"
    --
    module _ {{_ : isDiscrete I}} where
      hasIsoGetting:♮𝐒𝐮𝐛𝐬𝐭 : hasIsoGetting (♮𝐒𝐮𝐛𝐬𝐭 T)
      hasIsoGetting:♮𝐒𝐮𝐛𝐬𝐭 = hasIsoGetting:byFFEso hasIsoGetting:⧜𝐒𝐮𝐛𝐬𝐭

{-
-}
