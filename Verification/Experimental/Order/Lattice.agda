
-- {-# OPTIONS --overlapping-instances #-}

module Verification.Experimental.Order.Lattice where

open import Verification.Conventions
open import Verification.Experimental.Set.Setoid.Definition
-- open import Verification.Core.Category.Definition
-- open import Verification.Core.Category.Instance.Set.Definition
open import Verification.Experimental.Order.Preorder


module _ {A : 𝒰 _} {{_ : Preorder 𝑗 on A}} where
  _≚_ : A -> A -> 𝒰 _
  a ≚ b = (a ≤ b) ×-𝒰 (b ≤ a)

module _ {𝑖 : 𝔏 ^ 3} where
  record hasFiniteJoins (A : Preorder 𝑖) : 𝒰 𝑖 where
    field ⊥ : ⟨ A ⟩
          initial-⊥ : ∀{a : ⟨ A ⟩} -> ⊥ ≤ a
    field _∨_ : ⟨ A ⟩ -> ⟨ A ⟩ -> ⟨ A ⟩
          ι₀-∨ : {a b : ⟨ A ⟩} -> a ≤ a ∨ b
          ι₁-∨ : {a b : ⟨ A ⟩} -> b ≤ a ∨ b
          [_,_]-∨ : {a b c : ⟨ A ⟩} -> a ≤ c -> b ≤ c -> a ∨ b ≤ c

    infixl 60 _∨_
  open hasFiniteJoins {{...}} public

  record hasFiniteMeets (A : Preorder 𝑖) : 𝒰 𝑖 where
    field ⊤ : ⟨ A ⟩
          terminal-⊤ : ∀{a : ⟨ A ⟩} -> a ≤ ⊤
    field _∧_ : ⟨ A ⟩ -> ⟨ A ⟩ -> ⟨ A ⟩
          π₀-∧ : {a b : ⟨ A ⟩} -> a ∧ b ≤ a
          π₁-∧ : {a b : ⟨ A ⟩} -> a ∧ b ≤ b
          ⟨_,_⟩-∧ : {a b c : ⟨ A ⟩} -> c ≤ a -> c ≤ b -> c ≤ a ∧ b

    infixl 80 _∧_
  open hasFiniteMeets {{...}} public

  record hasAllJoins (𝑗 : 𝔏) (A : Preorder 𝑖) : 𝒰 (𝑖 ､ (𝑗 ⁺)) where
    field ⋁ : ∀{X : 𝒰 𝑗} -> (X -> ⟨ A ⟩) -> ⟨ A ⟩
          ι-⋁ : ∀{X F} -> ∀ (x : X) -> F x ≤ ⋁ F
          [_]-⋁ : ∀{X F b} -> (∀(x : X) -> F x ≤ b) -> ⋁ F ≤ b
  open hasAllJoins {{...}} public

  record hasAllMeets (𝑗 : 𝔏) (A : Preorder 𝑖) : 𝒰 (𝑖 ､ (𝑗 ⁺)) where
    field ⋀ : ∀{X : 𝒰 𝑗} -> (X -> ⟨ A ⟩) -> ⟨ A ⟩
          π-⋀ : ∀{X F} -> ∀ (x : X) -> ⋀ F ≤ F x
          ⟨_⟩-⋀ : ∀{X F b} -> (∀(x : X) -> b ≤ F x) -> b ≤ ⋀ F
  open hasAllMeets {{...}} public

CompleteJoinSemilattice : ∀ (𝑖 : 𝔏 ^ 4) -> 𝒰 (𝑖 ⁺)
CompleteJoinSemilattice 𝑖 = Preorder (𝑖 ⌄ 0 , 𝑖 ⌄ 1 , 𝑖 ⌄ 2) :& hasAllJoins (𝑖 ⌄ 3)

MeetSemilattice : ∀ 𝑖 -> 𝒰 (𝑖 ⁺)
MeetSemilattice 𝑖 = Preorder 𝑖 :& hasFiniteMeets

record isLattice (A : Preorder 𝑖 :& (hasFiniteMeets :, hasFiniteJoins)) : 𝒰 𝑖 where

instance
  isLattice:Default : ∀{A : 𝒰 _} -> {{_ : Preorder 𝑖 on A}}
                      {{_ : hasFiniteMeets ′ A ′}}
                      {{_ : hasFiniteJoins ′ A ′}}
                      -> isLattice ′ A ′
  isLattice:Default = record {}

Lattice : (𝑖 : 𝔏 ^ 3) -> 𝒰 _
Lattice 𝑖 = Preorder 𝑖 :& (hasFiniteMeets :, hasFiniteJoins) :& isLattice

----------------------------------------------------------
-- Derived instances

module _ {A : 𝒰 𝑖}
         {{_ : isSetoid {𝑗} A}}
         {{_ : isPreorder 𝑘 ′ A ′}}
         {{_ : hasFiniteJoins ′ A ′}} where
  instance
    hasFiniteJoins:Family : ∀{I : 𝒰 𝑗} -> hasFiniteJoins (′ (I -> A) ′)
    hasFiniteJoins.⊥         hasFiniteJoins:Family = λ _ -> ⊥
    hasFiniteJoins.initial-⊥ hasFiniteJoins:Family = incl ⟨ initial-⊥ ⟩
    hasFiniteJoins._∨_       hasFiniteJoins:Family = λ a b i -> a i ∨ b i
    hasFiniteJoins.ι₀-∨      hasFiniteJoins:Family = incl ⟨ ι₀-∨ ⟩
    hasFiniteJoins.ι₁-∨      hasFiniteJoins:Family = incl ⟨ ι₁-∨ ⟩
    hasFiniteJoins.[_,_]-∨   hasFiniteJoins:Family = λ f g -> incl ⟨ [ incl ⟨ f ⟩ , incl ⟨ g ⟩ ]-∨ ⟩



module _ {A : 𝒰 𝑖}
         {{_ : isSetoid {𝑗} A}}
         {{_ : isPreorder 𝑘 ′ A ′}}
         {{_ : hasFiniteMeets ′ A ′}} where
  instance
    hasFiniteMeets:Family : ∀{I : 𝒰 𝑗} -> hasFiniteMeets (′ (I -> A) ′)
    hasFiniteMeets.⊤          hasFiniteMeets:Family = λ _ -> ⊤
    hasFiniteMeets.terminal-⊤ hasFiniteMeets:Family = incl ⟨ terminal-⊤ ⟩
    hasFiniteMeets._∧_        hasFiniteMeets:Family = λ a b i -> a i ∧ b i
    hasFiniteMeets.π₀-∧       hasFiniteMeets:Family = incl ⟨ π₀-∧ ⟩
    hasFiniteMeets.π₁-∧       hasFiniteMeets:Family = incl ⟨ π₁-∧ ⟩
    hasFiniteMeets.⟨_,_⟩-∧    hasFiniteMeets:Family = λ f g -> incl ⟨ ⟨ incl ⟨ f ⟩ , incl ⟨ g ⟩ ⟩-∧ ⟩

  map-∧ : ∀{a b c d : A} -> (a ≤ b) -> (c ≤ d) -> a ∧ c ≤ b ∧ d
  map-∧ f g = ⟨ π₀-∧ ⟡ f , π₁-∧ ⟡ g ⟩-∧

  module _ {{_ : isPartialorder ′ A ′}} where
    _≀∧≀_ : {a b c d : A} -> (a ∼ b) -> (c ∼ d) -> a ∧ c ∼ b ∧ d
    _≀∧≀_ p q = antisym (map-∧ (by-∼-≤ p) (by-∼-≤ q)) (map-∧ (by-∼-≤ (p ⁻¹)) (by-∼-≤ (q ⁻¹)))

    sym-∧ : ∀{a b : A} -> a ∧ b ∼ b ∧ a
    sym-∧ = antisym (⟨ π₁-∧ , π₀-∧ ⟩-∧) (⟨ π₁-∧ , π₀-∧ ⟩-∧)

    unit-r-∧ : ∀{a : A} -> a ∧ ⊤ ∼ a
    unit-r-∧ = antisym π₀-∧ ⟨ reflexive , terminal-⊤ ⟩-∧

    unit-l-∧ : ∀{a : A} -> ⊤ ∧ a ∼ a
    unit-l-∧ = sym-∧ ∙ unit-r-∧

    assoc-l-∧ : ∀{a b c : A} -> (a ∧ b) ∧ c ∼ a ∧ (b ∧ c)
    assoc-l-∧ = antisym
      ⟨ π₀-∧ ⟡ π₀-∧ , ⟨ π₀-∧ ⟡ π₁-∧ , π₁-∧ ⟩-∧ ⟩-∧
      ⟨ ⟨ π₀-∧ , π₁-∧ ⟡ π₀-∧ ⟩-∧ , π₁-∧ ⟡ π₁-∧ ⟩-∧

    assoc-r-∧ : ∀{a b c : A} -> a ∧ (b ∧ c) ∼ (a ∧ b) ∧ c
    assoc-r-∧ = assoc-l-∧ ⁻¹

    idem-∧ : ∀{a : A} -> a ∧ a ∼ a
    idem-∧ = antisym π₀-∧ ⟨ reflexive , reflexive ⟩-∧

  ⋀-fin : ∀{n} -> (F : Fin-R n -> A) -> A
  ⋀-fin {zero} F = ⊤
  ⋀-fin {suc n} F = F zero ∧ (⋀-fin (λ i -> F (suc i)))


module _ {A : 𝒰 𝑖}
         {{_ : isSetoid {𝑗} A}}
         {{_ : isPreorder 𝑘 ′ A ′}}
         {{_ : hasAllJoins 𝑙 ′ A ′}} where
  instance
    hasAllJoins:Family : ∀{I : 𝒰 𝑗} -> hasAllJoins 𝑙 (′ (I -> A) ′)
    hasAllJoins.⋁ hasAllJoins:Family F = λ i -> ⋁ (λ x -> F x i)
    hasAllJoins.ι-⋁ hasAllJoins:Family = λ x → {!!}
    hasAllJoins.[ hasAllJoins:Family ]-⋁ = {!!}


  module _ {{_ : isPartialorder ′ A ′}}
         {{_ : hasFiniteJoins ′ A ′}} where

    empty-⋁ : ∀{B : 𝒰 𝑙} -> (B -> 𝟘-𝒰) -> {F : B -> A} -> ⋁ F ∼ ⊥
    empty-⋁ P {F} = antisym [ (λ b -> 𝟘-rec (P b)) ]-⋁ (initial-⊥)

    duplicate-r-⋁ : ∀{B : 𝒰 𝑙} -> {F : B -> A} -> (b : B) -> {a : A}
                    -> F b ∼ a -> ⋁ F ∨ a ∼ ⋁ F
    duplicate-r-⋁ b {a} p = antisym [ reflexive , (by-∼-≤ (p ⁻¹)) ⟡ ι-⋁ b ]-∨ (ι₀-∨)

module _ {A : 𝒰 𝑖}
         {{_ : isSetoid {𝑗} A}}
         {{_ : isPreorder 𝑘 ′ A ′}}
         {{_ : hasAllMeets 𝑙 ′ A ′}} where
  instance
    hasAllMeets:Family : ∀{I : 𝒰 𝑗} -> hasAllMeets 𝑙 (′ (I -> A) ′)
    hasAllMeets.⋀ hasAllMeets:Family F = λ i -> ⋀ (λ x -> F x i)
    hasAllMeets.π-⋀ hasAllMeets:Family = λ x → {!!}
    hasAllMeets.⟨ hasAllMeets:Family ⟩-⋀ = {!!}

module _ {A : 𝒰 𝑖}
         {{_ : isSetoid {𝑗} A}}
         {{_ : isPreorder 𝑘 ′ A ′}}
         {{_ : isPartialorder ′ A ′}}
         {{_ : hasFiniteJoins ′ A ′}}
         {{_ : hasFiniteMeets ′ A ′}} where

  absorb-l-∧ : ∀{a : A} -> ⊥ ∧ a ∼ ⊥
  absorb-l-∧ = antisym π₀-∧ initial-⊥

  absorb-r-∨ : ∀{a : A} -> a ∨ ⊤ ∼ ⊤
  absorb-r-∨ = antisym terminal-⊤ ι₁-∨




----------------------------------------------------------
-- Categorical Structure


-- unquoteDecl CompleteJoinSemilattice makeCompleteJoinSemilattice = #struct "CompleteJoinSemilattice" (quote hasAllJoins) "A" CompleteJoinSemilattice makeCompleteJoinSemilattice

-- instance
--   POStruc : ∀{a : CompleteJoinSemilattice 𝑖}


-- record isCompleteJoinPreserving {A : CompleteJoinSemilattice 𝑖} {B : CompleteJoinSemilattice 𝑗} (f : (⟨ A ⟩ -> El B) :& isMonotone {A = make& (⟨ A ⟩)}) : 𝒰 (𝑖 ､ 𝑗) where
--   testa : isPreorder (⟨ A ⟩)
--   testa = it


-- testing1 : (A : CompleteJoinSemilattice 𝑖) -> (X : 𝒰 𝑖) -> (F : X -> ⟨ A ⟩) -> 𝒰 𝑖
-- testing1 A X F = ∑ (λ (a : ⟨ A ⟩) -> ∀(x : X) -> a ≤ F x)


{-
record preservesAllJoins {A B} {{_ : CompleteJoinSemilattice 𝑖 on A}} {{_ : CompleteJoinSemilattice 𝑖 on B}} (f : (A -> B) :& isMonotone) : 𝒰 (𝑖 ⁺) where
  field preserves-⋁ : ∀{X} {F : X -> A} -> ⟨ f ⟩ (⋁ F) ≚ ⋁ (λ x -> ⟨ f ⟩ (F x))


record preservesFiniteMeets {A B} {{_ : MeetSemilattice 𝑖 on A}} {{_ : MeetSemilattice 𝑗 on B}} (f : (A -> B) :& isMonotone) : 𝒰 (𝑖 ､ 𝑗) where
  field preserves-∧ : ∀{a b : A} -> ⟨ f ⟩ (a ∧ b) ≚ ⟨ f ⟩ a ∧ ⟨ f ⟩ b
        preserves-⊤ : ⟨ f ⟩ ⊤ ≚ ⊤

-}

