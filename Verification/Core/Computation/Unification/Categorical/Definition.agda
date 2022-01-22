
module Verification.Core.Computation.Unification.Categorical.Definition where

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




module _ (𝒞 : Category 𝑖) where
  HomFamily : ∀ 𝑗 -> 𝒰 _
  HomFamily 𝑗 = ∀{a b : ⟨ 𝒞 ⟩} -> (f : a ⟶ b) -> 𝒰 𝑗

module _ {𝒞 : 𝒰 𝑖} {{_ : isCategory {𝑗} 𝒞}} where
  module _ {{_ : isZeroMorphismCategory ′ 𝒞 ′}} where

    record isPt {a b : 𝒞} (f : a ⟶ b) : 𝒰 (𝑖 ､ 𝑗) where
      constructor incl
      field ⟨_⟩ : f ∼ pt
      -- -> isPt {a} {b} f

    open isPt public


module _ {𝒞 : Category 𝑖} {{_ : isSizedCategory 𝒞}} {{_ : isZeroMorphismCategory 𝒞}} where

  isGood : HomFamily 𝒞 _
  isGood {a} {b} g = isPt g +-𝒰 (isId g +-𝒰 (sizeO b ≪ sizeO a))

  transp-isGood : ∀{a b : ⟨ 𝒞 ⟩} {f g : a ⟶ b} -> f ∼ g -> isGood f -> isGood g
  transp-isGood f∼g (left (incl f∼pt)) = left (incl (f∼g ⁻¹ ∙ f∼pt))
  transp-isGood f∼g (just (left (incl f∼id))) = just (left (incl (f∼g ⁻¹ ∙ f∼id)))
  transp-isGood f∼g (just (just x)) = just (just x)

  isGood:◆ : ∀{a b c : ⟨ 𝒞 ⟩} {f : a ⟶ b} {g : b ⟶ c} -> isGood f -> isGood g -> isGood (f ◆ g)
  isGood:◆ (left (incl f∼pt)) (q) = left (incl ((f∼pt ◈ refl) ∙ absorb-l-◆))
  isGood:◆ (just (left (incl f∼id))) q = transp-isGood (unit-l-◆ ⁻¹ ∙ (f∼id ⁻¹ ◈ refl)) q
  isGood:◆ (just (just x)) (left (incl g∼pt)) = left (incl ((refl ◈ g∼pt) ∙ absorb-r-◆))
  isGood:◆ (just (just x)) (just (left (incl _))) = just (just x)
  isGood:◆ (just (just x)) (just (just y)) = just (just (y ⟡-≪ x))


module _ {𝑖} {𝒞 : 𝒰 _} {{_ : 𝐙𝐌𝐂𝐚𝐭 𝑖 on 𝒞}} where
  UpFamily : (a : 𝒞) -> 𝒰 _
  UpFamily a = ∀{b : 𝒞} -> (a ⟶ b) -> 𝒰 (𝑖)

  record isIdeal (a : 𝒞) (P : ∀{b : 𝒞} -> (f : a ⟶ b) -> 𝒰 (𝑖)) : 𝒰 (𝑖) where
    field transp-Ideal : ∀{b} -> {f g : a ⟶ b} -> (p : f ∼ g) -> P f -> P g
    field ideal-r-◆ : ∀{b} -> {f : a ⟶ b} -> P f -> ∀{c} -> (g : b ⟶ c) -> P (f ◆ g)
    field ideal-pt : ∀{b} -> P {b} pt

  open isIdeal {{...}} public

  module _ (a : 𝒞) where
    Idealᵘ = _ :& isIdeal a
    macro Ideal = #structureOn Idealᵘ


  module _ {a : 𝒞} where

    record _∼-Ideal_ (A B : Ideal a) : 𝒰 (𝑖) where
      constructor incl
      field ⟨_⟩ : ∀{b} -> (f : a ⟶ b) -> ⟨ A ⟩ f ↔ ⟨ B ⟩ f

    open _∼-Ideal_ public
    -- _∼-Ideal_ : (A B : Ideal a) -> 𝒰 _
    -- _∼-Ideal_ A B = ∀{b} -> (f : a ⟶ b) -> ⟨ A ⟩ f ↔ ⟨ B ⟩ f

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

    record _≤-Ideal_ (A B : Ideal a) : 𝒰 (𝑖) where
      constructor incl
      field ⟨_⟩ : ∀{b} -> (f : a ⟶ b) -> ⟨ A ⟩ f -> ⟨ B ⟩ f

    open _≤-Ideal_ public

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

-----------------------------------------------------------------------------------------
-- The zero ideal

module _ {𝒞 : 𝒰 𝑖}
         {{_ : isCategory {𝑗} 𝒞}}
         {{_ : isZeroMorphismCategory ′ 𝒞 ′}}
         where
  -- private
  --   𝒞 = ⟨ 𝒞' ⟩

-- module _ {𝑖} {𝒞 : 𝒰 _} {{_ : 𝐙𝐌𝐂𝐚𝐭 𝑖 on 𝒞}} where
  module _ {a : 𝒞} where
    record ⊥-Idealᵘ {b : 𝒞} (f : a ⟶ b) : 𝒰 (𝑖 ､ 𝑗) where
      constructor incl
      field ⟨_⟩ : f ∼ pt

    open ⊥-Idealᵘ public

    macro
      ⊥-Ideal = #structureOn (λ {b} -> ⊥-Idealᵘ {b})


    instance
      isIdeal:⊥-Ideal : isIdeal a ⊥-Idealᵘ
      isIdeal:⊥-Ideal = record
        { transp-Ideal = λ f∼g (incl f∼pt) → incl (f∼g ⁻¹ ∙ f∼pt)
        ; ideal-r-◆     = λ (incl f∼pt) g → incl ((f∼pt ◈ refl) ∙ absorb-l-◆)
        ; ideal-pt      = incl refl
        }

    initial-⊥-Ideal : ∀{I : Ideal a} -> ′ (λ {b} -> ⊥-Idealᵘ {b}) ′ ≤ I
    initial-⊥-Ideal = incl λ f (incl f∼pt) → transp-Ideal (f∼pt ⁻¹) ideal-pt



-----------------------------------------------------------------------------------------
-- The semilattice structure


-- module _ {𝒞' : 𝐙𝐌𝐂𝐚𝐭 𝑖} where
module _ {𝒞 : 𝒰 𝑖}
         {{_ : isCategory {𝑗} 𝒞}}
         {{_ : isZeroMorphismCategory ′ 𝒞 ′}}
         where
  -- private
  --   𝒞 = ⟨ 𝒞' ⟩
  -- the meets
  module _ {a : 𝒞} (I J : Ideal a) where
    record _∧-Idealᵘ_ {b : 𝒞} (f : a ⟶ b) : 𝒰 (𝑖 ､ 𝑗) where
      constructor _,_
      field fst : ⟨ I ⟩ f
      field snd : ⟨ J ⟩ f

    open _∧-Idealᵘ_ public

    macro
      _∧-Ideal_ = #structureOn (λ {b} -> _∧-Idealᵘ_ {b})

  module _ {a : 𝒞} {I J : Ideal a} where
    instance
      isIdeal:∧-Ideal : isIdeal a (I ∧-Idealᵘ J)
      isIdeal:∧-Ideal = record
        { transp-Ideal = lem-1
        ; ideal-r-◆     = lem-2
        ; ideal-pt = ideal-pt , ideal-pt
        }
        where
          lem-1 : {b : 𝒞} {f g : a ⟶ b} → f ∼ g → (I ∧-Idealᵘ J) f → (I ∧-Idealᵘ J) g
          lem-1 p (A , B) = transp-Ideal p A , transp-Ideal p B

          lem-2 : {b : 𝒞} {f : a ⟶ b} → (I ∧-Idealᵘ J) f →
                  {c : 𝒞} (g : b ⟶ c) → (I ∧-Idealᵘ J) (f ◆ g)
          lem-2 (A , B) g = ideal-r-◆ A g , ideal-r-◆ B g

  -- the top element
  module _ {a : 𝒞} where
    record ⊤-Idealᵘ {b : 𝒞} (f : a ⟶ b) : 𝒰 (𝑖 ､ 𝑗) where
      constructor tt

    open ⊤-Idealᵘ public

    macro
      ⊤-Ideal = #structureOn (λ {b} -> ⊤-Idealᵘ {b})

    instance
      isIdeal:⊤-Ideal : isIdeal a ⊤-Ideal
      isIdeal:⊤-Ideal = record
        { transp-Ideal = λ p x → tt
        ; ideal-r-◆     = λ x g → tt
        }


    instance
      hasFiniteMeets:Ideal : hasFiniteMeets (Ideal a)
      hasFiniteMeets:Ideal = record
                                { ⊤ = ⊤-Ideal
                                ; terminal-⊤ = incl λ f x → tt
                                ; _∧_ = λ I J -> I ∧-Ideal J
                                ; π₀-∧ = incl λ f x → x .fst
                                ; π₁-∧ = incl λ f x → x .snd
                                ; ⟨_,_⟩-∧ = λ f g → incl λ h x → ⟨ f ⟩ h x , ⟨ g ⟩ h x
                                }

    module §-∧-Ideal where
      prop-1 : ∀{n : ℕ} {P : Fin-R n -> Ideal a} -> {x : 𝒞} {f : a ⟶ x} -> ⟨ ⋀-fin P ⟩ f -> ∀ i -> ⟨ P i ⟩ f
      prop-1 {zero} {P} {x} {f} f∈P ()
      prop-1 {suc n} {P} {x} {f} (f∈P0 , _   ) zero = f∈P0
      prop-1 {suc n} {P} {x} {f} (_    , f∈PS) (suc i) = prop-1 f∈PS i

      prop-2 : ∀{n : ℕ} {P : Fin-R n -> Ideal a} -> {x : 𝒞} {f : a ⟶ x} -> (∀ i -> ⟨ P i ⟩ f) -> ⟨ ⋀-fin P ⟩ f
      prop-2 {zero} {P} {x} {f} f∈Pi = tt
      prop-2 {suc n} {P} {x} {f} f∈Pi = f∈Pi zero , prop-2 (λ i -> f∈Pi (suc i))

      prop-3 : ∀{n : ℕ} -> ∀{b : 𝒞} -> {P : Fin-R n -> Ideal a} -> ⟨ ⋀-fin P ⟩ (pt {a = a} {b})
      prop-3 {P = P} = ideal-pt {{_}} {{of ⋀-fin P}}

-----------------------------------------------------------------------------------------
-- The forward action

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
        ; ideal-r-◆     = lem-2
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



-----------------------------------------------------------------------------------------
-- The inverse action

module _ {𝒞' : 𝐙𝐌𝐂𝐚𝐭 𝑖} where
  private
    𝒞 = ⟨ 𝒞' ⟩

  record _⁻¹↷ᵘ_ {a b : 𝒞} (f : a ⟶ b) (I : Ideal a) {x : 𝒞} (g : b ⟶ x) : 𝒰 (𝑖) where
    constructor incl
    field ⟨_⟩ : ⟨ I ⟩ (f ◆ g)

  open _⁻¹↷ᵘ_ public


  infixr 30 _⁻¹↷_
  _⁻¹↷_ : ∀{a b : 𝒞} -> (h : a ⟶ b) -> Ideal a -> Ideal b
  _⁻¹↷_ {a} {b} h I = (h ⁻¹↷ᵘ I) since P
    where
      lem-1 : {c : 𝒞} {f : b ⟶ c} {g : b ⟶ c} →
              f ∼ g → (h ⁻¹↷ᵘ I) f → (h ⁻¹↷ᵘ I) g
      lem-1 {c} {f} {g} f∼g (incl f∈hI) = incl (transp-Ideal (refl ◈ f∼g) f∈hI)

      lem-2 : {d : 𝒞} {f : b ⟶ d} →
                (h ⁻¹↷ᵘ I) f → {c : 𝒞} (g : d ⟶ c) → (h ⁻¹↷ᵘ I) (f ◆ g)
      lem-2 {d} {f} (incl f∈hI) {c} g =
        let P : ⟨ I ⟩ ((h ◆ f) ◆ g)
            P = ideal-r-◆ f∈hI g
            Q : ⟨ I ⟩ (h ◆ (f ◆ g))
            Q = transp-Ideal assoc-l-◆ P
        in incl Q

      P : isIdeal b _
      P = record
          { transp-Ideal = lem-1
          ; ideal-r-◆ = lem-2
          ; ideal-pt = incl (transp-Ideal (absorb-r-◆ ⁻¹) ideal-pt)
          }

  inv-↷-r : {a b : 𝒞} {f : a ⟶ b} -> {I : Ideal a} -> f ↷ (f ⁻¹↷ I) ∼ I ∧ (f ↷ ⊤-Ideal)
  inv-↷-r {a} {b} {f} {I} = antisym
    (incl (λ h (incl (e , incl e∈f⁻¹I , fe∼h)) → transp-Ideal (fe∼h) (e∈f⁻¹I)  , (incl (e , (tt , fe∼h)))))
    (incl λ h (h∈I , incl (e , tt , fe∼h)) → incl (e , (incl (transp-Ideal (fe∼h ⁻¹) h∈I) , fe∼h)))


-----------------------------------------------------------------------------------------
-- Epi principal

module _ {𝒞' : 𝐙𝐌𝐂𝐚𝐭 𝑖} {{_ : isSizedCategory ′ ⟨ 𝒞' ⟩ ′}} where

  private
    𝒞 = ⟨ 𝒞' ⟩

  isZeroOrEpi : ∀{a b : 𝒞} -> (f : a ⟶ b) -> 𝒰 _
  isZeroOrEpi f = (f ∼ pt) +-𝒰 (isEpi f)

  isZeroOrEpi:◆ : ∀{a b c : 𝒞} -> {f : a ⟶ b} {g : b ⟶ c} -> isZeroOrEpi f -> isZeroOrEpi g
                  -> isZeroOrEpi (f ◆ g)
  isZeroOrEpi:◆ (left f∼pt) q = left ((f∼pt ◈ refl) ∙ absorb-l-◆)
  isZeroOrEpi:◆ (just x) (left g∼pt) = left ((refl ◈ g∼pt) ∙ absorb-r-◆)
  isZeroOrEpi:◆ (just x) (just y) = just (isEpi:◆ x y)

-- module _ {𝒞 : 𝒰 𝑗} {{_ : isCategory {𝑖} 𝒞}} where
  module _ {a : 𝒞} where
    record isEpiPrincipal (I : Ideal a) : 𝒰 (𝑖) where
      field repObj : 𝒞
      field rep : a ⟶ repObj
      field principal-r : I ∼ rep ↷ ⊤-Ideal
      field isGoodRep : isGood rep
      field zeroOrEpi : isZeroOrEpi rep
      -- field factorPrinc : ∀{x} -> (f : a ⟶ x) -> ⟨ I ⟩ f -> ∑ λ (g : repObj ⟶ x) -> f ∼ rep ◆ g

    open isEpiPrincipal {{...}} public

    repObjOf : (I : Ideal a) {{_ : isEpiPrincipal I}} -> 𝒞
    repObjOf I = repObj

    repOf : (I : Ideal a) {{_ : isEpiPrincipal I}} -> a ⟶ repObjOf I
    repOf I = rep

    instance
      isEpiPrincipal:⊤ : isEpiPrincipal ⊤
      isEpiPrincipal:⊤ = record
        { repObj = a
        ; rep = id
        ; principal-r = antisym lem-1 terminal-⊤
        ; isGoodRep = right (left (incl refl))
        ; zeroOrEpi = right (isEpi:id)
        }
        where
          lem-1 : ⊤ ≤ (id ↷ ⊤)
          lem-1 = incl λ f x → incl (f , (x , unit-l-◆))

    transp-isEpiPrincipal : ∀{I J : Ideal a} -> (I ∼ J) -> isEpiPrincipal I -> isEpiPrincipal J
    transp-isEpiPrincipal {I} {J} I∼J P =
      let
        instance _ = P
      in record
        { repObj = repObjOf I
        ; rep = repOf I
        ; principal-r = I∼J ⁻¹ ∙ principal-r
        ; isGoodRep = isGoodRep
        ; zeroOrEpi = zeroOrEpi
        }

    instance
      isEpiPrincipal:⊥ : isEpiPrincipal ⊥-Ideal
      isEpiPrincipal:⊥ = record
        { repObj = a
        ; rep = pt
        ; principal-r = antisym initial-⊥-Ideal lem-1
        ; isGoodRep = left (incl refl)
        ; zeroOrEpi = left refl
        }
        where
          lem-1 : (pt {a = a} {a} ↷ ⊤-Ideal) ≤ ⊥-Ideal
          lem-1 = incl λ f (incl (e , tt , pt◆e∼f)) → incl (pt◆e∼f ⁻¹ ∙ absorb-l-◆)

    module §-EpiPrincipalᵣ where

      prop-1 : ∀{I : Ideal a} {{_ : isEpiPrincipal I}} -> repOf I ∼ pt -> I ∼ ⊥-Ideal
      prop-1 {I} p = principal-r ∙ (p ≀↷≀ refl) ∙ P
        where
          P : (pt {a = a} {repObjOf I} ↷ ⊤-Ideal) ∼ ⊥-Ideal
          P = antisym
              (incl (λ f (incl (e , _ , pt◆e∼f)) →
                let pt∼f : pt ∼ f
                    pt∼f = absorb-l-◆ ⁻¹ ∙ pt◆e∼f
                in incl (pt∼f ⁻¹)
              ))
              initial-⊥-Ideal

      prop-2 : ∀{I : Ideal a} {{_ : isEpiPrincipal I}} -> ⟨ I ⟩ (repOf I)
      prop-2 {I} {{IP}} = ⟨ by-∼-≤ (principal-r {{IP}} ⁻¹) ⟩ _ (incl (id , (tt , unit-r-◆)))

