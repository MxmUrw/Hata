
module Verification.Core.Computation.Unification.Categorical2.ForwardAction where

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
open import Verification.Core.Computation.Unification.Categorical2.Ideal


-----------------------------------------------------------------------------------------
-- The forward action

-- ===* Action of arrows on ideals
-- | Next, we turn our attention to how
--   arrows can act on ideals. Let |I : Ideal b|
--   be an ideal at |b|, and |f : a ⟶ b| an arrow.
--   Then we can construct a new ideal at |a|,
--   which we denote by |f ↷ I : Ideal a|.
--   This is defined to contain arrows of the
--   form |f ◆ h|, where |h| has to be in |I|.
-- | This construction is relevant because of the
--   following: let |t s : a ⟶ b| be two arrows
--   of which we know the mgu, call it |π : b ⟶ x|.
--   Then the ideal |J = π ↷ ⊤| consists of exactly those arrows
--   which factor through |π|, i.e., all elements |j| of |J| are of
--   the form |j ≡ π ◆ f| for some |f|. Obviously these arrows also
--   unify |t| and |s|, since |π| does. On the other hand,
--   every arrow |k : b ⟶ y| which unifies |t| and |s| has to factor
--   through |π|, by virtue of the universal property of coequalizers.
-- | This means that |π ↷ ⊤| contains exactly those arrows
--   which solve the same problem as that for which |π| is the most general
--   unifier.
-- | Turning the statement around, we can say the following: Given an ideal |I : Ideal b|
--   we are interested in finding an arrow |π : b ⟶ x|, such that all arrows in |I| factor
--   through |π|, or equivalently, such that |I ∼ (π ↷ ⊤)| holds.
--   The reason for our interest is that, in the case that |I = CoeqIdeal t s|,
--   the above equation almost means that |π| is the coequalizer of |t| and |s|.
--   The only thing missing is the requirement for |π| to be an epimorphism.
--
-- | \medskip
--
-- | This gives us a characterization of mgu's where
--   the requirement that all unifiers should factor through
--   the most general one is packaged in the equation |I ∼ (π ↷ ⊤)|.
--

-- [Hide]
module _ {𝒞' : 𝐙𝐌𝐂𝐚𝐭 𝑖} where
  private
    𝒞 = ⟨ 𝒞' ⟩

  module _ {a b : 𝒞} (f : a ⟶ b) (I : Ideal b) where

    record _↷ᵘ_ {x : 𝒞} (g : a ⟶ x) : 𝒰 (𝑖) where
      constructor incl
      field ⟨_⟩ : ∑ λ (h : b ⟶ x) -> ⟨ I ⟩ h ×-𝒰 (f ◆ h ∼ g)

    open _↷ᵘ_ public

    -- macro _↷_ = #structureOn (λ {x} -> _↷ᵘ_ {x})


  module _ {a b : 𝒞} {h : a ⟶ b} {I : Ideal b} where
    instance
      isIdeal:↷ : isIdeal a (h ↷ᵘ I)
      isIdeal:↷ = record
        { transp-Ideal = lem-1
        ; ideal-r-◆     = λ a b -> lem-2 a b
        ; ideal-pt = incl (pt , (ideal-pt , absorb-r-◆))
        }
        where
          lem-1 : {b : 𝒞} {f : a ⟶ b} {g : a ⟶ b} →
                  f ∼ g → (h ↷ᵘ I) f → (h ↷ᵘ I) g
          lem-1 f∼g (incl (e , e∈I , he∼f)) = incl (e , (e∈I , he∼f ∙ f∼g))

          lem-2 : {d : 𝒞} {f : a ⟶ d} → (h ↷ᵘ I) f → {c : 𝒞} (g : d ⟶ c) → (h ↷ᵘ I) (f ◆ g)
          lem-2 {d} {f} (incl (e , e∈I , he∼f)) {c} g =
            let P : h ◆ (e ◆ g) ∼ f ◆ g
                P = h ◆ (e ◆ g)  ⟨ assoc-r-◆ ⟩-∼
                    (h ◆ e) ◆ g  ⟨ he∼f ◈ refl ⟩-∼
                    f ◆ g        ∎
            in incl (e ◆ g , (ideal-r-◆ e∈I g , P))

  infixr 30 _↷_
  _↷_ : ∀{a b : 𝒞} -> (f : a ⟶ b) -> Ideal b -> Ideal a
  _↷_ f I = ′ f ↷ᵘ I ′

  _≀↷≀_ : ∀{a b : 𝒞} -> {f g : a ⟶ b} -> f ∼ g -> {I J : Ideal b} -> I ∼ J -> f ↷ I ∼ g ↷ J
  _≀↷≀_ {a} {b} {f} {g} f∼g {I} {J} I∼J = antisym
    (incl (λ h (incl (e , e∈I , fe∼h)) →
      let e∈J : ⟨ J ⟩ e
          e∈J = ⟨ I∼J ⟩ e .fst e∈I
          ge∼h : g ◆ e ∼ h
          ge∼h = (f∼g ⁻¹ ◈ refl) ∙ fe∼h
      in incl (e , (e∈J , ge∼h))
    ))
    (incl (λ h (incl (e , e∈J , ge∼h)) →
      let e∈I : ⟨ I ⟩ e
          e∈I = ⟨ I∼J ⁻¹ ⟩ e .fst e∈J
          fe∼h : f ◆ e ∼ h
          fe∼h = (f∼g ◈ refl) ∙ ge∼h
      in incl (e , (e∈I , fe∼h))
    ))

  assoc-l-↷ : ∀{a b c : 𝒞} {f : a ⟶ b} {g : b ⟶ c} -> {I : Ideal c} -> (f ◆ g) ↷ I ∼ f ↷ (g ↷ I)
  assoc-l-↷ {a} {b} {c} {f} {g} {I} = antisym
    (incl (λ h (incl (e , e∈I , fge∼h)) → incl (g ◆ e , ((incl (e , (e∈I , refl))) , assoc-r-◆ ∙ fge∼h))))
    (incl λ h (incl (ge' , (incl (e , e∈I , ge∼ge')) , fge'∼h)) → incl (e , (e∈I ,
      let P : f ◆ g ◆ e ∼ h
          P = assoc-l-◆ ∙ (refl ◈ ge∼ge') ∙ fge'∼h
      in P
      )))

-- //


