
module Verification.Experimental.Algebra.MonoidWithZero.Ideal where

open import Verification.Conventions

open import Verification.Experimental.Set.Setoid.Definition
open import Verification.Experimental.Set.Setoid.Subsetoid
open import Verification.Experimental.Order.Preorder
open import Verification.Experimental.Order.Lattice
open import Verification.Experimental.Data.Prop.Everything
open import Verification.Experimental.Data.Universe.Everything
open import Verification.Experimental.Algebra.Monoid.Definition
open import Verification.Experimental.Algebra.MonoidWithZero.Definition
open import Verification.Experimental.Algebra.MonoidAction.Definition


record isIdeal-r {𝑗 : 𝔏 ^ 2} (A : Monoid₀ 𝑗) (P : 𝒫 ⟨ A ⟩ :& isSubsetoid) : 𝒰 𝑗 where
  field ideal-◍ : ◍ ∈ P -- ⟨ ⟨ P ⟩ ◍ ⟩
  field ideal-r-⋆ : ∀{a : ⟨ A ⟩} -> a ∈ P -> ∀ b -> (a ⋆ b) ∈ P
  -- ⟨ ⟨ P ⟩ (a ⋆ b) ⟩
open isIdeal-r {{...}} public

Ideal-r : (A : Monoid₀ 𝑗) -> 𝒰 _
Ideal-r A = _ :& isIdeal-r A

module _ {A : 𝒰 _} {{_ : Monoid₀ 𝑖 on A}} where
  ZeroOrCancel-r : A -> 𝒰 _
  ZeroOrCancel-r a = (a ∼ ◍) +-𝒰 ((a ≁ ◍) ×-𝒰 ∀{b c : A} -> a ⋆ b ∼ a ⋆ c -> b ∼ c)


module _ {A : Monoid₀ 𝑖} where
  private
    _∼-Ideal_ : Ideal-r A -> Ideal-r A -> 𝒰 _
    _∼-Ideal_ = _∼-hasU_

  instance
    isEquivRel:∼-Ideal : isEquivRel (∼-Base _∼-Ideal_)
    isEquivRel:∼-Ideal = isEquivRel:hasU

  instance
    isSetoid:Ideal-r : isSetoid _ (Ideal-r A)
    isSetoid:Ideal-r = isSetoid:hasU

  instance
    isIdeal-r:⊤ : isIdeal-r A ⊤
    isIdeal-r.ideal-◍ isIdeal-r:⊤ = tt
    isIdeal-r.ideal-r-⋆ isIdeal-r:⊤ _ _ = tt


  instance
    isPreorder:Ideal-r : isPreorder _ ′(Ideal-r A)′
    isPreorder._≤'_ isPreorder:Ideal-r I J = ⟨ I ⟩ ≤' ⟨ J ⟩
    isPreorder.reflexive isPreorder:Ideal-r = incl (λ a -> a)
    isPreorder._⟡_ isPreorder:Ideal-r p q = incl (λ a -> ⟨ q ⟩ (⟨ p ⟩ a)) -- ⟨( incl ⟨ p ⟩ ⟡ incl ⟨ q ⟩)⟩
    isPreorder.transp-≤ isPreorder:Ideal-r p q X = incl ⟨ transp-≤ (incl ⟨ p ⟩) (incl ⟨ q ⟩) (incl ⟨ X ⟩) ⟩

  instance
    isPartialorder:Ideal-r : isPartialorder ′(Ideal-r A)′
    isPartialorder:Ideal-r = record
      { antisym = λ p q -> incl ⟨ antisym (incl ⟨ p ⟩) (incl ⟨ q ⟩) ⟩
      }

  -- instance
  --   hasAllJoins:Ideal-r : hasAllJoins _ ′(Ideal-r A)′
  --   hasAllJoins.⋁ hasAllJoins:Ideal-r F = {!!}
  --   hasAllJoins.ι-⋁ hasAllJoins:Ideal-r = {!!}
  --   hasAllJoins.[ hasAllJoins:Ideal-r ]-⋁ = {!!}

  record _∧-Ideal-r_ (I J : Ideal-r A) (a : ⟨ A ⟩) : 𝒰 𝑖 where
    constructor _,_
    field fst : a ∈ I
    field snd : a ∈ J

  instance
    isIdeal-r:∧ : ∀{I J : 𝒫 ⟨ A ⟩} -> {{_ : Ideal-r A on I}} {{_ : Ideal-r A on J}} -> isIdeal-r A (′ I ′ ∧ ′ J ′)
    isIdeal-r:∧ = record
      { ideal-◍ = ideal-◍ , ideal-◍
      ; ideal-r-⋆ = λ (p , q) a -> ideal-r-⋆ p a , ideal-r-⋆ q a
      }


  instance
    hasFiniteMeets:Ideal-r : hasFiniteMeets ′(Ideal-r A)′
    hasFiniteMeets.⊤ hasFiniteMeets:Ideal-r = ′ ⊤ ′
    hasFiniteMeets.terminal-⊤ hasFiniteMeets:Ideal-r = incl (λ x → tt)
    hasFiniteMeets._∧_ hasFiniteMeets:Ideal-r I J = ′ ⟨ I ⟩ ∧ ⟨ J ⟩ ′
    hasFiniteMeets.π₀-∧ hasFiniteMeets:Ideal-r = incl fst -- incl ⟨ π₀-∧ ⟩
    hasFiniteMeets.π₁-∧ hasFiniteMeets:Ideal-r = incl snd -- incl ⟨ π₁-∧ ⟩
    hasFiniteMeets.⟨_,_⟩-∧ hasFiniteMeets:Ideal-r = λ f g -> incl (λ x → (⟨ f ⟩ x , ⟨ g ⟩ x))


module _ {A : Monoid₀ (𝑖 , 𝑖)} where
  -- instance
  --   isSetoid:Ideal-r : isSetoid _ (Ideal-r A)
  --   isSetoid:Ideal-r = isSetoid:hasU
  -- ∃ x ∶ (x ∈ I) ∧ (b ∼ a ⋆ x)

  -- module _ (a : ⟨ A ⟩) (I : 𝒫 ⟨ A ⟩) where
  --   _↷-Ide'_ : 𝒫 ⟨ A ⟩
  --   _↷-Ide'_ = λ b -> ∣ (∑ λ x -> ⟨ I x ⟩ ×-𝒰 (b ∼ a ⋆ x)) ∣

  record _↷-Ide''_ (a : ⟨ A ⟩) (I : Ideal-r A) (b : ⟨ A ⟩) : 𝒰 𝑖 where
    constructor incl
    field ⟨_⟩  : (∑ λ x -> (x ∈ I) ∧ (b ∼ a ⋆ x))
    -- field ⟨_⟩  : ∃ x ∈ I ∶ (b ∼ a ⋆ x)

  module _ (a : ⟨ A ⟩) (I : Ideal-r A) where
    _↷-Ide'_ : 𝒫 ⟨ A ⟩
    _↷-Ide'_ = λ b -> ∣ (a ↷-Ide'' I) b ∣


  -- _↷-Ide'_ a I = λ b -> ∃ x ∈ I ∶ (b ∼ a ⋆ x)
  -- _↷-Ide'_ a I = λ b -> ∣ (∑ λ x -> (x ∈ I) ×-𝒰 (b ∼ a ⋆ x)) ∣

    -- module _ {a : ⟨ A ⟩} {I : 𝒫 ⟨ A ⟩} {{_ : Ideal-r A on I}} where
  module _ {a : ⟨ A ⟩} {I : 𝒫 ⟨ A ⟩}
    {{_ : isSubsetoid I}}
    {{_ : isIdeal-r A ′ I ′}} where
  -- module _ {a : ⟨ A ⟩} {I : Ideal-r A} where
    instance
      -- isSubsetoid:↷-Ide' : isSubsetoid (λ x -> ∣ ⟨ (a ↷-Ide' I) x ⟩ ∣-Prop)
      isSubsetoid:↷-Ide' : isSubsetoid ((a ↷-Ide' ′ I ′))
      isSubsetoid.transp-Subsetoid isSubsetoid:↷-Ide' {b} {c} p (incl (x , Ix , q)) = incl (x , Ix , p ⁻¹ ∙ q)

    instance
      -- isIdeal-r:↷-Ide' : isIdeal-r A (′ (λ x -> ∣ ⟨ (a ↷-Ide' I) x ⟩ ∣-Prop) ′ {{isSubsetoid:↷-Ide'}})
      isIdeal-r:↷-Ide' : isIdeal-r A ′(a ↷-Ide' ′ I ′)′
      isIdeal-r:↷-Ide' = record
        { ideal-◍ = incl (◍ , ideal-◍ , absorb-r-⋆ ⁻¹)
        ; ideal-r-⋆ = λ {y} -> λ (incl (x , x∈I , xP)) b → incl $
                    (x ⋆ b) ,
                    ideal-r-⋆ x∈I b ,
                    (let P₀ : y ⋆ b ∼ a ⋆ (x ⋆ b)
                         P₀ = (xP ≀⋆≀ refl) ∙ assoc-l-⋆
                     in P₀)
        }

  -- module _ (a : ⟨ A ⟩) (I : 𝒫 ⟨ A ⟩)
  --   {{_ : isSubsetoid I}}
  --   {{_ : isIdeal-r A ′ I ′}} where
  --   _↷-Ide_ : Ideal-r A
  --   _↷-Ide_ = ′ (λ x -> ∣ ⟨ (a ↷-Ide' ′ I ′) x ⟩ ∣-Prop) ′

  _↷-Ide_ : (a : ⟨ A ⟩) -> (I : Ideal-r A) -> Ideal-r A
  -- _↷-Ide_ a I = ′ (λ x -> ∣ ⟨ (a ↷-Ide' I) x ⟩ ∣-Prop) ′
  _↷-Ide_ a I = ′(a ↷-Ide' I)′

  instance
    hasAction-l:Ideal-r : hasAction-l ′ ⟨ A ⟩ ′ ′ Ideal-r A ′
    hasAction-l._↷_ hasAction-l:Ideal-r = _↷-Ide_
    hasAction-l.assoc-l-↷ hasAction-l:Ideal-r {m} {n} {I} =
      let P₀ : ((m ⋆ n) ↷ I) ≤ (m ↷ (n ↷ I))
          P₀ = incl (λ (incl (x , x∈I , xP)) → incl $ (n ⋆ x) , (incl (x , x∈I , refl) , (xP ∙ assoc-l-⋆)))
          P₁ : (m ↷ (n ↷ I)) ≤ ((m ⋆ n) ↷ I)
          P₁ = incl (λ {a} (incl (x , (incl (y , y∈I , yP)) , xP)) → incl $ y , y∈I , (
                    let P₂ : a ∼ (m ⋆ n) ⋆ y
                        P₂ = a           ⟨ xP ⟩-∼
                             m ⋆ x       ⟨ refl ≀⋆≀ yP ⟩-∼
                             m ⋆ (n ⋆ y) ⟨ assoc-r-⋆ ⟩-∼
                            (m ⋆ n) ⋆ y  ∎
                    in P₂
               ))
      in antisym P₀ P₁
    hasAction-l._≀↷≀_ hasAction-l:Ideal-r {m} {n} {I} {J} p q =
      let P₀ : (m ↷ I) ≤ (n ↷ J)
          P₀ = incl (λ (incl (x , x∈I , xP)) → incl $ x , ⟨ by-∼-≤ q ⟩ x∈I  , (xP ∙ (p ≀⋆≀ refl)))
          P₁ : (n ↷ J) ≤ (m ↷ I)
          P₁ = incl (λ (incl (x , x∈I , xP)) → incl $ x , ⟨ by-∼-≤ (q ⁻¹) ⟩ x∈I  , (xP ∙ (p ⁻¹ ≀⋆≀ refl)))
      in antisym P₀ P₁

  record _⁻¹↷-Ide''_ (a : ⟨ A ⟩) (I : Ideal-r A) (x : ⟨ A ⟩) : 𝒰 𝑖 where
    constructor incl
    field ⟨_⟩  : (a ⋆ x) ∈ I

  open _⁻¹↷-Ide''_ {{...}} public

  _⁻¹↷-Ide'_ : (a : ⟨ A ⟩) -> (I : Ideal-r A) -> 𝒫 ⟨ A ⟩
  _⁻¹↷-Ide'_ a I = λ x → ∣ (a ⁻¹↷-Ide'' I) x ∣

  -- _⁻¹↷-Ide'_ : (a : ⟨ A ⟩) -> (I : Ideal-r A) -> 𝒫 ⟨ A ⟩
  -- _⁻¹↷-Ide'_ a I = λ x → ∣ (a ⋆ x) ∈ I ∣

  -- module _ {a : ⟨ A ⟩} {I : 𝒫 ⟨ A ⟩} {{_ : Ideal-r A on I}} where
  module _ {a : ⟨ A ⟩} {I : 𝒫 ⟨ A ⟩}
    {{_ : isSubsetoid I}}
    {{_ : isIdeal-r A ′ I ′}} where
    instance
      isSubsetoid:⁻¹↷-Ide' : isSubsetoid (a ⁻¹↷-Ide' ′ I ′)
      isSubsetoid.transp-Subsetoid isSubsetoid:⁻¹↷-Ide' {x} {y} x∼y x∈I = incl (transp-Subsetoid (refl ≀⋆≀ x∼y) ⟨ x∈I ⟩)

    instance
      isIdeal-r:⁻¹↷-Ide' : isIdeal-r A ′(a ⁻¹↷-Ide' ′ I ′)′
      isIdeal-r.ideal-◍   isIdeal-r:⁻¹↷-Ide' = incl (transp-Subsetoid (absorb-r-⋆ ⁻¹) ideal-◍)
      isIdeal-r.ideal-r-⋆ isIdeal-r:⁻¹↷-Ide' {b} b∈a⁻¹I c =
        let P₀ : a ⋆ (b ⋆ c) ∈ I
            P₀ = transp-Subsetoid assoc-l-⋆ (ideal-r-⋆ ⟨ b∈a⁻¹I ⟩ c)
        in incl P₀

  _⁻¹↷-Ide_ : (a : ⟨ A ⟩) -> (I : Ideal-r A) -> Ideal-r A
  _⁻¹↷-Ide_ a I = ′(a ⁻¹↷-Ide' I)′ {{isIdeal-r:⁻¹↷-Ide' {a = a} {I = ⟨ I ⟩}}}

  inv-↷Ide-r : {a : ⟨ A ⟩} -> {I : Ideal-r A} -> a ↷ (a ⁻¹↷-Ide I) ∼ I ∧ (a ↷ ⊤)
  inv-↷Ide-r {a} {I} =
    let P₀ : (a ↷ (a ⁻¹↷-Ide I)) ≤ (I ∧ (a ↷ ⊤))
        P₀ = incl (λ (incl (x , x∈a⁻¹I , xP)) → transp-Subsetoid (xP ⁻¹) ⟨ x∈a⁻¹I ⟩ , incl (x , tt , xP))
        P₁ : (I ∧ (a ↷ ⊤)) ≤ (a ↷ (a ⁻¹↷-Ide I))
        P₁ = incl (λ {b} (x , (incl (z , _ , zP))) → incl $ z , (incl (transp-Subsetoid zP x) , zP))
    in antisym P₀ P₁

  absorb-l-⁻¹↷-Ide : {I : Ideal-r A} -> (◍ ⁻¹↷-Ide I) ∼ ⊤
  absorb-l-⁻¹↷-Ide {I} =
    let P₁ : ⊤ ≤ (◍ ⁻¹↷-Ide I)
        P₁ = incl (λ x → incl (transp-Subsetoid (absorb-l-⋆ ⁻¹) ideal-◍))
    in antisym terminal-⊤ P₁


  unit-l-⁻¹↷-Ide : {I : Ideal-r A} -> (◌ ⁻¹↷-Ide I) ∼ I
  unit-l-⁻¹↷-Ide {I} =
    let P₀ : (◌ ⁻¹↷-Ide I) ≤ I
        P₀ = incl (λ (incl x) → transp-Subsetoid unit-l-⋆ x)
        P₁ : I ≤ (◌ ⁻¹↷-Ide I)
        P₁ = incl (λ x → incl (transp-Subsetoid (unit-l-⋆ ⁻¹) x))
    in antisym P₀ P₁

  unit-r-⁻¹↷-Ide : {a : ⟨ A ⟩} -> (a ⁻¹↷-Ide ⊤) ∼ ⊤
  unit-r-⁻¹↷-Ide {a} =
    let P₀ : ⊤ ≤ (a ⁻¹↷-Ide ⊤)
        P₀ = incl (λ x → incl tt)
        P₁ : (a ⁻¹↷-Ide ⊤) ≤ ⊤
        P₁ = incl (λ x → tt)
    in antisym P₁ P₀

  -- module _ {I J : 𝒫 ⟨ A ⟩} {{_ : isSubsetoid I}} {{_ : isSubsetoid J}}
  --   {{_ : isIdeal-r A ′ I ′}}
  --   {{_ : isIdeal-r A ′ J ′}}
  --   where
  -- module _ {I J : 𝒫 ⟨ A ⟩} {{_ : Ideal-r A on I}} {{_ : Ideal-r A on J}} where
    -- distr-↷-∧-Ide : {a : ⟨ A ⟩} -> (a ↷ (′ I ′ ∧ ′ J ′)) ∼ ((a ↷ ′ I ′) ∧ (a ↷ ′ J ′))

  distr-↷-∧-Ide : {a : ⟨ A ⟩} -> {I J : Ideal-r A} -> (ZeroOrCancel-r a) -> (a ↷ (I ∧ J)) ∼ ((a ↷ I) ∧ (a ↷ J))
  distr-↷-∧-Ide {a} {I} {J} P =
    let P₀ : (a ↷ (I ∧ J)) ≤ ((a ↷ I) ∧ (a ↷ J))
        P₀ = incl (λ (incl (x , (x∈I , x∈J) , xP)) → (incl (x , x∈I , xP)) , (incl (x , x∈J , xP)))
        P₁ = incl (λ {b} (incl (x , x∈I , xP) , incl (y , y∈J , yP)) →
          let Q₀ = case P of
                      (λ a∼◍ ->
                        let Q₁ : b ∼ a ⋆ ◍
                            Q₁ = b      ⟨ xP ⟩-∼
                                 a ⋆ x  ⟨ a∼◍ ≀⋆≀ refl ⟩-∼
                                 ◍ ⋆ x  ⟨ absorb-l-⋆ ⟩-∼
                                 ◍      ⟨ absorb-r-⋆ ⁻¹ ⟩-∼
                                 a ⋆ ◍  ∎

                        in incl (◍ , ideal-◍ , Q₁)
                      )
                      (λ (a≁◍ , cancel-a) -> let Q₁ : a ⋆ x ∼ a ⋆ y
                                                 Q₁ = xP ⁻¹ ∙ yP
                                                 Q₂ : x ∼ y
                                                 Q₂ = cancel-a Q₁
                                                 Q₃ : x ∈ (I ∧ J)
                                                 Q₃ = (x∈I , transp-Subsetoid (Q₂ ⁻¹) y∈J)

                                             in incl (x , Q₃ , xP))

          in Q₀)
    in antisym P₀ P₁



module _ {𝑖 : 𝔏} {A : Monoid₀ (𝑖 , 𝑖)} where

  record isPrincipal-r (I : Ideal-r A) : 𝒰 (𝑖 ⁺) where
    field rep : ⟨ A ⟩
    field principal-r : I ∼ (rep ↷ ′ ⊤ ′)
  open isPrincipal-r {{...}} public

  Principal-r::rep-in-ideal : ∀{I : Ideal-r A} -> {{_ : isPrincipal-r I}} -> ⟨ ⟨ I ⟩ rep ⟩
  Principal-r::rep-in-ideal {I} =
    let P₀ = inv-∼-Setoid ⟨ principal-r ⟩ (incl (◌ , tt , unit-r-⋆ ⁻¹))
    in P₀

  rep' : (I : Ideal-r A) -> {{_ : isPrincipal-r I}} -> ⟨ A ⟩
  rep' I = rep

Principal-r : (Monoid₀ (𝑖 , 𝑖)) -> 𝒰 _
Principal-r A = Ideal-r A :& isPrincipal-r

module _ {𝑖 : 𝔏} {A : Monoid₀ (𝑖 , 𝑖)} where

  record isEpiPrincipal (I : Ideal-r A) : 𝒰 𝑖 where

module _ {𝑖 : 𝔏} {A : Monoid₀ (𝑖 , 𝑖)} where

  instance
    isPrincipal-r:⊤ : isPrincipal-r {A = A} ⊤
    isPrincipal-r:⊤ = record
      { rep = ◌
      ; principal-r = antisym
        (incl (λ {a} x → incl $ a , tt , unit-l-⋆ ⁻¹))
        (incl (λ x → tt))
      }

  record isPrincipal⁺-r (Good : Submonoid ′ ⟨ A ⟩ ′) (I : Principal-r A) : 𝒰 𝑖 where
    field zeroOrCancel-r : ZeroOrCancel-r (rep {{of I}})
    field isGood : ⟨ ⟨ Good ⟩ (rep {{of I}}) ⟩
  open isPrincipal⁺-r {{...}} public

  isPrincipal/⁺-r : (Good : Submonoid ′ ⟨ A ⟩ ′) -> (I : Ideal-r A) -> 𝒰 _
  isPrincipal/⁺-r Good = isPrincipal-r :> isPrincipal⁺-r Good

  transp-isPrincipal-r : ∀{I J : Ideal-r A} -> (I ∼ J) -> isPrincipal-r I -> isPrincipal-r J
  transp-isPrincipal-r I∼J pI = record
    { rep = rep {{pI}}
    ; principal-r = I∼J ⁻¹ ∙ principal-r {{pI}}
    }

  transp-isPrincipal/⁺-r : ∀{I J : Ideal-r A} {Good : Submonoid ′ ⟨ A ⟩ ′} -> (I ∼ J) -> isPrincipal/⁺-r Good I -> isPrincipal/⁺-r Good J
  transp-isPrincipal/⁺-r {I} {J} {Good} I∼J PI =
    let instance
          P₀ : isPrincipal-r ′ ⟨ J ⟩ ′
          P₀ = transp-isPrincipal-r I∼J it
          P₁ : isPrincipal⁺-r Good ′ ⟨ J ⟩ ′
          P₁ = record { zeroOrCancel-r = zeroOrCancel-r {{_:>_.Proof2> PI}} ; isGood = isGood {{_:>_.Proof2> PI}} }
    in it


  module _ {{_ : zeroIsDecidable A}} where
    instance
      isPrincipal⁺-r:⊤ : {Good : Submonoid ′ ⟨ A ⟩ ′} -> isPrincipal⁺-r Good ′ ⊤ ′
      isPrincipal⁺-r:⊤ = record
        { zeroOrCancel-r = case decide-◍ ◌ of
                                (λ (◌≁◍) ->
                                  let P : ∀{b c} -> (◌ ⋆ b) ∼ ◌ ⋆ c -> b ∼ c
                                      P p = unit-l-⋆ ⁻¹ ∙ p ∙ unit-l-⋆
                                  in right (◌≁◍ , P))
                                (λ (◌∼◍) -> left ◌∼◍)
        ; isGood = closed-◌
        }

    closed-⋆-ZeroOrCancel-r : ∀{a b : ⟨ A ⟩} -> ZeroOrCancel-r a -> ZeroOrCancel-r b -> ZeroOrCancel-r (a ⋆ b)
    closed-⋆-ZeroOrCancel-r (left x) y = left ((x ≀⋆≀ refl) ∙ absorb-l-⋆)
    closed-⋆-ZeroOrCancel-r (just x) (left y) = left ((refl ≀⋆≀ y) ∙ absorb-r-⋆)
    closed-⋆-ZeroOrCancel-r {a} {b} (just (a≁◍ , cancel-a)) (just (b≁◍ , cancel-b)) with decide-◍ (a ⋆ b)
    ... | just x = left x
    ... | left (a≁b) =
      let P₀ : ∀{x y : ⟨ A ⟩} -> (a ⋆ b) ⋆ x ∼ (a ⋆ b) ⋆ y -> x ∼ y
          P₀ {x} {y} p =
            let q : a ⋆ (b ⋆ x) ∼ a ⋆ (b ⋆ y)
                q = assoc-r-⋆ ∙ p ∙ assoc-l-⋆
            in cancel-b (cancel-a q)

      in right (a≁b , P₀)


  -- record isBoth (Good : Submonoid ′ ⟨ A ⟩ ′) (I : Ideal-r A) : 𝒰 (𝑖 ⁺) where
  --   field {{BothOne}} : isPrincipal-r I
  --   field BothTwo : isPrincipal⁺-r Good (′ ⟨ I ⟩ ′)

  -- open isBoth public

  -- isSubsetoid:isPrincipal/⁺-r : isSubsetoid (isPrincipal/⁺-r)
  -- isSubsetoid:isPrincipal/⁺-r = ?

  -- isPrincipal-r : (I : Ideal-r A) -> 𝒰 _
  -- isPrincipal-r I = 




-- record hasUniqueSolution {A : 𝒰 𝑖} {{_ : isSetoid 𝑗 A}} (P : A -> 𝒰 𝑘) : 𝒰 (𝑖 ､ 𝑗 ､ 𝑘) where
--   field ⟨_⟩ : ∑ P
--   field isUniqueSolution : ∀(x : ∑ P) -> fst x ∼ fst ⟨_⟩




