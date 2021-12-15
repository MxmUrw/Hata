
module Verification.Core.Algebra.MonoidWithZero.Ideal.Instance.hasAction where

open import Verification.Conventions

open import Verification.Core.Set.Setoid.Definition
open import Verification.Core.Set.Setoid.Subsetoid
open import Verification.Core.Order.Preorder
open import Verification.Core.Order.Lattice
open import Verification.Core.Data.Prop.Everything
open import Verification.Core.Algebra.Monoid.Definition
open import Verification.Core.Algebra.MonoidWithZero.Definition
open import Verification.Core.Algebra.MonoidAction.Definition
open import Verification.Core.Algebra.MonoidWithZero.Ideal.Definition
open import Verification.Core.Algebra.MonoidWithZero.Ideal.Instance.Lattice



module _ {A : Monoid₀ (𝑖 , 𝑖)} where
  record _↷-Idealᵘ_ (a : ⟨ A ⟩) (I : Ideal A) (b : ⟨ A ⟩) : 𝒰 𝑖 where
    constructor incl
    field ⟨_⟩  : (∑ λ x -> (x ∈ I) ×-𝒰 (b ∼ a ⋆ x))

  module _ (a : ⟨ A ⟩) (I : Ideal A) where
    infixr 30 _↷-Ideal_
    macro _↷-Ideal_ = #structureOn (↓𝒫 (a ↷-Idealᵘ I))


  -- module _ {a : ⟨ A ⟩} {I : 𝒫 ⟨ A ⟩}
  --   {{_ : isSubsetoid I}}
  --   {{_ : isIdeal A ′ I ′}} where
  module _ {a : ⟨ A ⟩} {I : Ideal A} where
    instance
      -- isSubsetoid:↷-Ideal : isSubsetoid ((a ↷-Ideal ′ I ′))
      isSubsetoid:↷-Ideal : isSubsetoid (a ↷-Ideal I)
      isSubsetoid.transp-Subsetoid isSubsetoid:↷-Ideal {b} {c} p (incl (x , Ix , q)) = incl (x , Ix , p ⁻¹ ∙ q)

      -- isIdeal:↷-Ideal : isIdeal A (′ (λ x -> ∣ ⟨ (a ↷-Ideal I) x ⟩ ∣-Prop) ′ {{isSubsetoid:↷-Ideal}})
    instance
      isIdeal:↷-Ideal : isIdeal A (a ↷-Ideal I)
      isIdeal:↷-Ideal = record
        { ideal-◍ = incl (◍ , ideal-◍ , absorb-r-⋆ ⁻¹)
        ; ideal-r-⋆ = λ {y} -> λ (incl (x , x∈I , xP)) b → incl $
                    (x ⋆ b) ,
                    ideal-r-⋆ x∈I b ,
                    (let P₀ : y ⋆ b ∼ a ⋆ (x ⋆ b)
                         P₀ = (xP ≀⋆≀ refl) ∙ assoc-l-⋆
                     in P₀)
        }


  -- infixr 30 _↷-Idealᵉ_
  -- _↷-Idealᵉ_ : (a : ⟨ A ⟩) -> (I : Ideal A) -> Ideal A
  -- _↷-Idealᵉ_ a I = a ↷-Ideal I


  instance
    hasActionₗ:Ideal : hasActionₗ ′ ⟨ A ⟩ ′ (Ideal A)

    hasActionₗ._↷_ hasActionₗ:Ideal
      = λ a I -> a ↷-Ideal I

    hasActionₗ.assoc-l-↷  hasActionₗ:Ideal {m} {n} {I}
      = antisym P₀ P₁
      where
        P₀ : ((m ⋆ n) ↷ I) ≤ (m ↷ (n ↷ I))
        P₀ = λ _ -> incl (λ (incl (x , x∈I , xP)) → incl $ (n ⋆ x) , (incl (x , x∈I , refl) , (xP ∙ assoc-l-⋆)))

        P₁ : (m ↷ n ↷ I) ≤ (m ⋆ n ↷ I)
        ⟨ P₁ a ⟩ (incl (x , (incl (y , y∈I , yP)) , xP)) = incl $ y , y∈I , yP'
          where
            yP' : a ∼ (m ⋆ n) ⋆ y
            yP'  = a           ⟨ xP ⟩-∼
                  m ⋆ x       ⟨ refl ≀⋆≀ yP ⟩-∼
                  m ⋆ (n ⋆ y) ⟨ assoc-r-⋆ ⟩-∼
                  (m ⋆ n) ⋆ y ∎

    hasActionₗ._≀↷≀_       hasActionₗ:Ideal {m} {n} {I} {J} p q =
      let P₀ : (m ↷ I) ≤ (n ↷ J)
          P₀ = λ _ -> incl (λ (incl (x , x∈I , xP)) → incl $ x , ⟨ by-∼-≤ (⟨ q ⟩) ⟩ x∈I  , (xP ∙ (p ≀⋆≀ refl)))
          P₁ : (n ↷ J) ≤ (m ↷ I)
          P₁ = λ _ -> incl (λ (incl (x , x∈I , xP)) → incl $ x , ⟨ by-∼-≤ ⟨ q ⁻¹ ⟩ ⟩ x∈I  , (xP ∙ (p ⁻¹ ≀⋆≀ refl)))
      in antisym P₀ P₁


  -- distributivity
  distr-↷-∧-Ide : {a : ⟨ A ⟩} -> {I J : Ideal A} -> (isZeroOrEpi a) -> (a ↷ (I ∧ J)) ∼ ((a ↷ I) ∧ (a ↷ J))
  distr-↷-∧-Ide {a} {I} {J} P =
    let P₀ : (a ↷ (I ∧ J)) ≤ ((a ↷ I) ∧ (a ↷ J))
        P₀ = λ _ -> incl (λ (incl (x , (x∈I , x∈J) , xP)) → (incl (x , x∈I , xP)) , (incl (x , x∈J , xP)))
        -- P₁ = incl (λ {b} (incl (x , x∈I , xP) , incl (y , y∈J , yP)) →
        --   let Q₀ = case P of
        --               (λ a∼◍ ->
        --                 let Q₁ : b ∼ a ⋆ ◍
        --                     Q₁ = b      ⟨ xP ⟩-∼
        --                          a ⋆ x  ⟨ a∼◍ ≀⋆≀ refl ⟩-∼
        --                          ◍ ⋆ x  ⟨ absorb-l-⋆ ⟩-∼
        --                          ◍      ⟨ absorb-r-⋆ ⁻¹ ⟩-∼
        --                          a ⋆ ◍  ∎

        --                 in incl (◍ , ideal-◍ , Q₁)
        --               )
        --               (λ (a≁◍ , cancel-a) -> let Q₁ : a ⋆ x ∼ a ⋆ y
        --                                          Q₁ = xP ⁻¹ ∙ yP
        --                                          Q₂ : x ∼ y
        --                                          Q₂ = cancel-a Q₁
        --                                          Q₃ : x ∈ (I ∧ J)
        --                                          Q₃ = (x∈I , transp-Subsetoid (Q₂ ⁻¹) y∈J)

        --                                      in incl (x , Q₃ , xP))

        --   in Q₀)
    in {!!} -- antisym P₀ P₁




--------------------------------------------------------------------------------------------------------------
-- There is an additional inverse action


  record _⁻¹↷-Ide''_ (a : ⟨ A ⟩) (I : Ideal A) (x : ⟨ A ⟩) : 𝒰 𝑖 where
    constructor incl
    field ⟨_⟩  : (a ⋆ x) ∈ I

  open _⁻¹↷-Ide''_ {{...}} public

  _⁻¹↷-Ide'_ : (a : ⟨ A ⟩) -> (I : Ideal A) -> 𝒫 ⟨ A ⟩
  _⁻¹↷-Ide'_ a I = λ x → ∣ (a ⁻¹↷-Ide'' I) x ∣

  -- _⁻¹↷-Ide'_ : (a : ⟨ A ⟩) -> (I : Ideal A) -> 𝒫 ⟨ A ⟩
  -- _⁻¹↷-Ide'_ a I = λ x → ∣ (a ⋆ x) ∈ I ∣

  -- module _ {a : ⟨ A ⟩} {I : 𝒫 ⟨ A ⟩} {{_ : Ideal A on I}} where
  module _ {a : ⟨ A ⟩} {I : 𝒫 ⟨ A ⟩}
    {{_ : isSubsetoid I}}
    {{_ : isIdeal A ′ I ′}} where
    instance
      isSubsetoid:⁻¹↷-Ide' : isSubsetoid (a ⁻¹↷-Ide' ′ I ′)
      isSubsetoid.transp-Subsetoid isSubsetoid:⁻¹↷-Ide' {x} {y} x∼y x∈I = incl (transp-Subsetoid (refl ≀⋆≀ x∼y) ⟨ x∈I ⟩)

    instance
      isIdeal:⁻¹↷-Ide' : isIdeal A ′(a ⁻¹↷-Ide' ′ I ′)′
      isIdeal.ideal-◍   isIdeal:⁻¹↷-Ide' = incl (transp-Subsetoid (absorb-r-⋆ ⁻¹) ideal-◍)
      isIdeal.ideal-r-⋆ isIdeal:⁻¹↷-Ide' {b} b∈a⁻¹I c =
        let P₀ : a ⋆ (b ⋆ c) ∈ I
            P₀ = transp-Subsetoid assoc-l-⋆ (ideal-r-⋆ ⟨ b∈a⁻¹I ⟩ c)
        in incl P₀

  _⁻¹↷-Ide_ : (a : ⟨ A ⟩) -> (I : Ideal A) -> Ideal A
  _⁻¹↷-Ide_ a I = ′(a ⁻¹↷-Ide' I)′ {{isIdeal:⁻¹↷-Ide' {a = a} {I = ⟨ I ⟩}}}

  inv-↷Ide-r : {a : ⟨ A ⟩} -> {I : Ideal A} -> a ↷ (a ⁻¹↷-Ide I) ∼ I ∧ (a ↷ ⊤)
  inv-↷Ide-r {a} {I} =
    let P₀ : (a ↷ (a ⁻¹↷-Ide I)) ≤ (I ∧ (a ↷ ⊤))
        P₀ = {!!} -- incl (λ (incl (x , x∈a⁻¹I , xP)) → transp-Subsetoid (xP ⁻¹) ⟨ x∈a⁻¹I ⟩ , incl (x , tt , xP))
        P₁ : (I ∧ (a ↷ ⊤)) ≤ (a ↷ (a ⁻¹↷-Ide I))
        P₁ = {!!} -- incl (λ {b} (x , (incl (z , _ , zP))) → incl $ z , (incl (transp-Subsetoid zP x) , zP))
    in antisym P₀ P₁

  absorb-l-⁻¹↷-Ide : {I : Ideal A} -> (◍ ⁻¹↷-Ide I) ∼ ⊤
  absorb-l-⁻¹↷-Ide {I} =
    let P₁ : ⊤ ≤ (◍ ⁻¹↷-Ide I)
        P₁ = {!!} -- incl (λ x → incl (transp-Subsetoid (absorb-l-⋆ ⁻¹) ideal-◍))
    in {!!} --  antisym terminal-⊤ P₁


  unit-l-⁻¹↷-Ide : {I : Ideal A} -> (◌ ⁻¹↷-Ide I) ∼ I
  unit-l-⁻¹↷-Ide {I} =
    let P₀ : (◌ ⁻¹↷-Ide I) ≤ I
        P₀ = {!!} -- incl (λ (incl x) → transp-Subsetoid unit-l-⋆ x)
        P₁ : I ≤ (◌ ⁻¹↷-Ide I)
        P₁ = {!!} -- incl (λ x → incl (transp-Subsetoid (unit-l-⋆ ⁻¹) x))
    in antisym P₀ P₁

  unit-r-⁻¹↷-Ide : {a : ⟨ A ⟩} -> (a ⁻¹↷-Ide ⊤) ∼ ⊤
  unit-r-⁻¹↷-Ide {a} =
    let P₀ : ⊤ ≤ (a ⁻¹↷-Ide ⊤)
        P₀ = λ _ -> incl (λ x → incl tt)
        P₁ : (a ⁻¹↷-Ide ⊤) ≤ ⊤
        P₁ = λ _ -> incl (λ x → tt)
    in antisym P₁ P₀



