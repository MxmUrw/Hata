
module Verification.Experimental.Data.Substitution.Normal.Definition where

open import Verification.Experimental.Conventions hiding (_⊔_)

open import Verification.Experimental.Set.Setoid.Definition
open import Verification.Experimental.Set.Discrete
open import Verification.Experimental.Set.Set.Definition
open import Verification.Experimental.Set.Function.Injective
open import Verification.Experimental.Set.Setoid.Morphism
open import Verification.Experimental.Set.Setoid.Morphism.Property
open import Verification.Experimental.Set.Contradiction
open import Verification.Experimental.Set.Function.Property
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

open import Verification.Experimental.Data.Nat.Free
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
open import Verification.Experimental.Category.Std.RelativeMonad.KleisliCategory.Instance.IsoGetting
open import Verification.Experimental.Data.FiniteIndexed.Property.IsoGetting

open import Verification.Experimental.Data.Substitution.Definition

-- lists
module _ {A : 𝒰 𝑖} where
  data _∍♮_ : ∀(as : List A) -> (a : A) -> 𝒰 𝑖 where
    incl : ∀{a bs} -> (a ∷ bs) ∍♮ a
    skip : ∀{a b bs} -> bs ∍♮ a ->  (b ∷ bs) ∍♮ a

  -- ι-∍♮ : ∀{as : List A} {a} -> as ∍♮ a -> ι as ∍ a
  -- ι-∍♮ = {!!}



-- dependent lists

module _ {A : 𝒰 𝑖} (B : A -> 𝒰 𝑗) where
  data DList : (as : List A) -> 𝒰 (𝑖 ､ 𝑗) where
    [] : DList []
    _∷_ : ∀{a as} -> (b : B a) -> (bs : DList as) -> DList (a ∷ as)

module _ {A : 𝒰 𝑖} {B : A -> 𝒰 𝑗} where


  -- construct-DList : ∀{as : List A} -> (∀ a -> as ∍♮ a -> B a) -> DList B as
  -- construct-DList {⦋⦌} f = []
  -- construct-DList {x ∷ as} f = (f x incl) ∷ (construct-DList (λ a x -> f a (skip x)))

  -- destruct-DList : ∀{as : List A} -> DList B as -> (∀ a -> as ∍♮ a -> B a)
  -- destruct-DList {⦋⦌} [] a ()
  -- destruct-DList {x ∷ as} (b ∷ xs) .x incl = b
  -- destruct-DList {x ∷ as} (b ∷ xs) a (skip p) = destruct-DList xs a p

  construct-DList-人DList : ∀{as : List A} -> D人List B (ι as) -> DList B as
  construct-DList-人DList {⦋⦌} xs = []
  construct-DList-人DList {x ∷ as} (incl x₁ ⋆-⧜ xs₁) = x₁ ∷ (construct-DList-人DList xs₁)

  destruct-DList-人DList : ∀{as : List A} -> DList B as -> D人List B (ι as)
  destruct-DList-人DList {⦋⦌} xs = ◌-⧜
  destruct-DList-人DList {x ∷ as} (b ∷ xs) = incl b ⋆-⧜ destruct-DList-人DList xs

  inv-l-◆-construct-DList : ∀{as : List A} -> (r : D人List B (ι as)) -> destruct-DList-人DList (construct-DList-人DList r) ≡ r
  inv-l-◆-construct-DList {⦋⦌} ◌-⧜ = λ i → ◌-⧜
  inv-l-◆-construct-DList {x ∷ as} (incl x₁ ⋆-⧜ xs₁) = λ i → (incl x₁) ⋆-⧜ (inv-l-◆-construct-DList xs₁ i)

  inv-r-◆-construct-DList : ∀{as : List A} -> (f : DList B as) -> construct-DList-人DList (destruct-DList-人DList f) ≡ f
  inv-r-◆-construct-DList {⦋⦌} [] = λ i → []
  inv-r-◆-construct-DList {x ∷ as} (b ∷ xs) = λ i → b ∷ inv-r-◆-construct-DList xs i



module _ {A : 𝒰 𝑖}  where
  DListHom : (B : List A -> A -> 𝒰 𝑗) -> List A -> List A -> 𝒰 _
  DListHom B as bs = DList (B bs) as


-- list based inductive substitutions

record NormalInductiveSubstitution {I : 𝒰 𝑖} (T : RelativeMonad (𝑓𝑖𝑛 I)) : 𝒰 𝑖 where
  constructor incl
  field ⟨_⟩ : List I

open NormalInductiveSubstitution {{...}} public

module _ {I : 𝒰 𝑖} (T : RelativeMonad (𝑓𝑖𝑛 I)) where
  macro ♮𝐒𝐮𝐛𝐬𝐭 = #structureOn (NormalInductiveSubstitution T)


module _ {I : 𝒰 𝑖} {T' : RelativeMonad (𝑓𝑖𝑛 I)} where

  private macro T = #structureOn ⟨ T' ⟩

  private
    RT : List I -> I -> 𝒰 _
    RT = (λ b a → ix (T (incl (ι b))) a)

  Hom-♮𝐒𝐮𝐛𝐬𝐭' : (a b : ♮𝐒𝐮𝐛𝐬𝐭 T) -> 𝒰 𝑖
  Hom-♮𝐒𝐮𝐛𝐬𝐭' a b = DListHom RT ⟨ a ⟩ ⟨ b ⟩

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
      isSetoid:Hom-♮𝐒𝐮𝐛𝐬𝐭 = isSetoid:byStrId


    map-ι-♮𝐒𝐮𝐛𝐬𝐭 : (f : Hom-♮𝐒𝐮𝐛𝐬𝐭 a b) -> (ι a ⟶ ι b)
    map-ι-♮𝐒𝐮𝐛𝐬𝐭 (♮subst f) = ⧜subst (destruct-DList-人DList f)

  instance
    isSetoidHom:map-ι-♮𝐒𝐮𝐛𝐬𝐭 : {a b : NormalInductiveSubstitution ′ ⟨ T' ⟩ ′} →
                                  isSetoidHom ′ Hom-♮𝐒𝐮𝐛𝐬𝐭 a b ′
                                  ′ incl (ι ⟨ a ⟩) ⟶ incl (ι ⟨ b ⟩) ′
                                  map-ι-♮𝐒𝐮𝐛𝐬𝐭
    isSetoidHom:map-ι-♮𝐒𝐮𝐛𝐬𝐭 = record { cong-∼ = λ {refl-≣ → refl-≣} }

    isInjective:map-ι-♮𝐒𝐮𝐛𝐬𝐭 : {a b : NormalInductiveSubstitution ′ ⟨ T' ⟩ ′} → isInjective (map-ι-♮𝐒𝐮𝐛𝐬𝐭 {a = a} {b = b})
    isInjective:map-ι-♮𝐒𝐮𝐛𝐬𝐭 {a} {b} = record { cancel-injective = λ p -> cong-Str ♮subst (lem-1 (lem-2 p)) }
      where
        lem-2 : ∀{a b} -> ∀{f g : Hom-⧜𝐒𝐮𝐛𝐬𝐭 {T = T} a b} -> ⧜subst {T = T} f ≣ ⧜subst g -> f ≣ g
        lem-2 refl-≣ = refl-≣


        lem-1 : ∀{a b} -> ∀{f g : Hom-♮𝐒𝐮𝐛𝐬𝐭' a b} -> destruct-DList-人DList f ≣ destruct-DList-人DList g -> f ≣ g
        lem-1 {f = []} {[]} p = refl-≣
        lem-1 {f = b ∷ f} {b₁ ∷ g} p with §-D人List.prop-1 p
        ... | refl-≣ , Y with lem-1 Y
        ... | refl-≣ = refl-≣


  surj-map-ι-♮𝐒𝐮𝐛𝐬𝐭 : ∀{a b : ♮𝐒𝐮𝐛𝐬𝐭 T} -> ι a ⟶ ι b -> Hom-♮𝐒𝐮𝐛𝐬𝐭 a b
  surj-map-ι-♮𝐒𝐮𝐛𝐬𝐭 f = ♮subst (construct-DList-人DList ⟨ f ⟩)

  inv-surj-map-ι-♮𝐒𝐮𝐛𝐬𝐭 : ∀{a b : ♮𝐒𝐮𝐛𝐬𝐭 T} -> ∀{f : ι a ⟶ ι b} -> map-ι-♮𝐒𝐮𝐛𝐬𝐭 (surj-map-ι-♮𝐒𝐮𝐛𝐬𝐭 f) ∼ f
  inv-surj-map-ι-♮𝐒𝐮𝐛𝐬𝐭 = cong-Str ⧜subst (≡→≡-Str (inv-l-◆-construct-DList _))

  instance
    isSurjective:map-ι-♮𝐒𝐮𝐛𝐬𝐭 : ∀{a b : ♮𝐒𝐮𝐛𝐬𝐭 T} -> isSurjective (map-ι-♮𝐒𝐮𝐛𝐬𝐭 {a} {b})
    isSurjective:map-ι-♮𝐒𝐮𝐛𝐬𝐭 = surjective surj-map-ι-♮𝐒𝐮𝐛𝐬𝐭 inv-surj-map-ι-♮𝐒𝐮𝐛𝐬𝐭



  id-♮𝐒𝐮𝐛𝐬𝐭 : ∀{a} -> Hom-♮𝐒𝐮𝐛𝐬𝐭 a a
  id-♮𝐒𝐮𝐛𝐬𝐭 = ♮subst (construct-DList-人DList (id-⧜𝐒𝐮𝐛𝐬𝐭' {T = T}))

  _◆-♮𝐒𝐮𝐛𝐬𝐭_ : ∀{a b c} -> Hom-♮𝐒𝐮𝐛𝐬𝐭 a b -> Hom-♮𝐒𝐮𝐛𝐬𝐭 b c -> Hom-♮𝐒𝐮𝐛𝐬𝐭 a c
  ♮subst f ◆-♮𝐒𝐮𝐛𝐬𝐭 ♮subst g = ♮subst (construct-DList-人DList (_◆-⧜𝐒𝐮𝐛𝐬𝐭''_ {T = T} (destruct-DList-人DList f) (destruct-DList-人DList g)))

  private
    lem-1 : {a b c : NormalInductiveSubstitution ′ ⟨ T' ⟩ ′}
            {f : Hom-♮𝐒𝐮𝐛𝐬𝐭 a b} {g : Hom-♮𝐒𝐮𝐛𝐬𝐭 b c} →
            (it isSetoid.∼ map-ι-♮𝐒𝐮𝐛𝐬𝐭 (f ◆-♮𝐒𝐮𝐛𝐬𝐭 g))
            (map-ι-♮𝐒𝐮𝐛𝐬𝐭 f ◆-⧜𝐒𝐮𝐛𝐬𝐭 map-ι-♮𝐒𝐮𝐛𝐬𝐭 g)
    lem-1 {a}{b}{c}{f}{g} = ≡→≡-Str (cong ⧜subst ( inv-l-◆-construct-DList _))

    lem-2 : {a : NormalInductiveSubstitution ′ ⟨ T' ⟩ ′} → (it isSetoid.∼ map-ι-♮𝐒𝐮𝐛𝐬𝐭 (id-♮𝐒𝐮𝐛𝐬𝐭 {a = a})) id-⧜𝐒𝐮𝐛𝐬𝐭
    lem-2 = ≡→≡-Str (cong ⧜subst (inv-l-◆-construct-DList _))


  instance
    isCategory:♮𝐒𝐮𝐛𝐬𝐭 : isCategory (♮𝐒𝐮𝐛𝐬𝐭 T)
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
        -- in 𝐈𝐱
        lem-04 : 𝑒𝑙 (ι (♮ ⟨ d ⟩)) ≅ 𝑒𝑙 ⟨ d ⟩
        lem-04 = cong-∼ surj-♮-Free-𝐌𝐨𝐧

        d'' : 𝐅𝐢𝐧𝐈𝐱 _
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


