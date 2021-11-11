

module Verification.Old.Core.Algebra.Action.Combination where

open import Verification.Conventions
open import Verification.Old.Core.Category.Definition
open import Verification.Old.Core.Category.Instance.Set.Definition
open import Verification.Old.Core.Category.Instance.Set.Equalizers
open import Verification.Old.Core.Category.Instance.Type
open import Verification.Old.Core.Category.Idempotent
-- open import Verification.Old.Core.Category.Instance.TypeProperties
open import Verification.Old.Core.Homotopy.Level
open import Verification.Old.Core.Algebra.Basic.Abelian
open import Verification.Old.Core.Algebra.Basic.Group
open import Verification.Old.Core.Algebra.Basic.Monoid
open import Verification.Old.Core.Algebra.Basic.Ring
open import Verification.Old.Core.Order.Totalorder
open import Verification.Old.Core.Order.Preorder
open import Verification.Old.Core.Order.Lattice
-- open import Verification.Old.Core.Type.Instance.Nat
open import Verification.Old.Core.Type.Instance.Int
open import Verification.Old.Core.Type.Instance.Sum
open import Verification.Old.Core.Type.Decidable

Functor:List : ∀{𝑖} -> Functor ` 𝒰 𝑖 ` ` 𝒰 𝑖 `
⟨ Functor:List ⟩ = List
IFunctor.map (of Functor:List) = map-List
IFunctor.functoriality-id (of Functor:List) = {!!}
IFunctor.functoriality-◆ (of Functor:List) = {!!}
IFunctor.functoriality-≣ (of Functor:List) = {!!}

instance IFunctor:List = #openstruct Functor:List

--------------------------------------------------------------------
-- "Norms"

record INormed (V : Totalorder 𝑖) (A : 𝒰 𝑗) : 𝒰 (𝑖 ､ 𝑗) where
  field size : A -> ⟨ V ⟩
open INormed {{...}} public

instance
  INotation:Absolute:INormed : ∀{V : Totalorder 𝑖} {A : 𝒰 𝑗} {{_ : INormed V A}} -> Notation-Absolute A ⟨ V ⟩
  Notation-Absolute.∣ INotation:Absolute:INormed ∣ = size


--------------------------------------------------------------------
-- Pre polynomials

module _ (A : 𝒰 𝑖) (X : 𝒰 𝑗) {{_ : IAbelian A}} {{_ : ITotalorder X}} where
  PreCombination : 𝒰 (𝑖 ､ 𝑗)
  PreCombination = List (A ×-𝒰 X)




instance
  Cast:right : ∀{A : 𝒰 𝑖} {B : 𝒰 𝑖} -> Cast B IAnything (A +-𝒰 B)
  Cast.cast Cast:right b = right b

  Cast:List : ∀{A : 𝒰 𝑖} -> Cast A IAnything (List A)
  Cast.cast Cast:List a = a ∷ []


private
  module _ {A : 𝒰 𝑖} {X : 𝒰 𝑗} {{_ : IAbelian A}} {{_ : IDiscrete A}}
           {{_ : ITotalorder X}} {{_ : IDec-Totalorder X}} where

    negate : PreCombination A X -> PreCombination A X
    negate = map f
      where f : A ×-𝒰 X -> A ×-𝒰 X
            f (a , x) = - a , x

    Val = Lift {j = 𝑗} 𝟙-𝒰 +-𝒰 X

    -- `0` : Val
    -- `0` = left (↥ tt)

    norm : PreCombination A X -> Val
    norm [] = ⊥
    norm ((a , x) ∷ p) = right x ∨ norm p

    instance
      INormed:PreCombination : INormed ` Val ` (PreCombination A X)
      INormed.size INormed:PreCombination = norm

    data isSorted : PreCombination A X -> 𝒰 (𝑖 ､ 𝑗) where
      [] : isSorted []
      append : ∀{x : X} {a : A} -> (a ≡ 𝟶 -> 𝟘-𝒰) -> {as : PreCombination A X} -> ∣ as ∣ < ` x ` -> isSorted as -> isSorted ((a , x) ∷ as)

    prependIfNotZero : (a : A ×-𝒰 X) -> (p : ∑ isSorted) -> (∣ fst p ∣ < ` a .snd `) -> ∑ isSorted
    prependIfNotZero (a , x) (p , pp) p<x with (a ≡ 𝟶) ？
    ... | no a≠0 = (a , x) ∷ p , append a≠0 p<x pp
    ... | yes a=0 = p , pp


    insert : (a : A ×-𝒰 X) -> (p : PreCombination A X) -> (isSorted p) -> ∑ isSorted

    insert-norm : ∀(a : A ×-𝒰 X) -> (p : PreCombination A X) -> (pp : isSorted p) -> ∣ fst (insert a p pp) ∣ ≤ ∣ p ∣ ∨ ` snd a `

    insert (a , x) p pp with ask ((a ≡ 𝟶) ？)
    ... | yes x₁ = (p , pp)
    insert (a , x) [] [] | no a≠0 = ((a , x) ∷ []) , append a≠0 (left-right-≤ , left≢right) []
    insert (a , x) ((a2 , x₂) ∷ p) (append a2≠0 ap pp) | no a≠0 with (x₂ ≤ x) ？ | (x₂ ≡ x) ？
    ... | X | yes x₂=x = prependIfNotZero (a + a2 , x₂) (p , pp) ap
    ... | yes x₂≤x | no x₂≠x = (a , x) ∷ (a2 , x₂) ∷ p , append a≠0 (P2 , P3) (append a2≠0 ap pp)
                              where P1 : (` x₂ ` ∨ ∣ p ∣) ≡ ` x₂ `
                                    P1 = sym-max {a = just x₂} {b = norm p} ∙ (max-reduce-r {a = norm p} {b = just x₂} (ap .fst))
                                    P2 : (` x₂ ` ∨ ∣ p ∣) ≤ ` x `
                                    P2 = transport (λ i -> P1 (~ i) ≤ just x) (right-≤ x₂≤x)

                                    P3 : (` x₂ ` ∨ ∣ p ∣) ≡ ` x ` -> 𝟘-𝒰
                                    P3 = transport (λ i -> P1 (~ i) ≡ just x -> 𝟘-𝒰) (λ p -> x₂≠x (isInjective:right p))

    ... | no x₂≰x | no x₁ = (a2 , x₂) ∷ (fst p-rec) , append a2≠0 P3 (snd p-rec)
      where p-rec = insert (a , x) p pp
            p' = fst p-rec


            P1 : ∣ p ∣ ∨ ` x ` ≡ ` x₂ ` -> 𝟘-𝒰
            P1 qq with ask (decide {{IDec-Totalorder.Impl2 it {a = norm p} {b = just x}}} )
            -- (norm p ≤ just x) ？)
            ... | no x = ap .snd qq
            ... | yes x = x₁ (isInjective:right (qq ⁻¹))
              -- where
              --   P0-1 : just x ≤ just x₂
              --   P0-1 = trans-≤ (ι₁-max {a = ∣ p ∣}) (≡→≤ qq)

            P2 : ∣ p ∣ ∨ ` x ` < ` x₂ `
            P2 = max-initial (ap .fst) (≤-switch (λ {(right-≤ ξ) -> x₂≰x ξ})) , P1

            P3 : ∣ p' ∣ < ` x₂ `
            P3 = trans-≤ (insert-norm (a , x) p pp) (fst P2) , ({!!})
            -- transport (λ i -> insert-norm (a , x) p pp (~ i) < just x₂) P2

    insert-norm (a , x) p pp with ask ((a ≡ 𝟶) ？)
    ... | yes x₁ = {!!}
    ... | no x₁ = {!!}

    -- (a + a2 , x₂) ∷ p , append {!!} ap pp  -- (a , x) ∷ (a2 , x₂) ∷ p , append a≠0 {!!} (append a2≠0 ap pp)


-- ([] , []) 
--     ... | left a≠0 = ((a , x) ∷ []) , append a≠0 (↥ tt , left≢right) []
--     ... | just x₁ = [] , []
--     insert (a , x) ((a2 , x₂) ∷ p , append a2≠0 ap pp) with (x₂ ≤ x) ？
--     ... | left x₃ = (a , x) ∷ (a2 , x₂) ∷ p , append {!!} {!!} (append a2≠0 ap pp)
--     ... | just x₃ = {!!}

private
  module _ (A : 𝒰 𝑖) (X : 𝒰 𝑗) {{_ : IAbelian A}} {{_ : IDiscrete A}}
           {{_ : ITotalorder X}} {{_ : IDec-Totalorder X}} where
    sort' : PreCombination A X -> ∑ isSorted
    sort' [] = [] , []
    sort' (x ∷ p) = insert x (fst p') (snd p')
      where p' = sort' p

    sort : PreCombination A X -> PreCombination A X
    sort p = sort' p .fst

    idempotent-sort : ∀ p -> sort (sort p) ≡ sort p
    idempotent-sort = {!!}

    Set:PreCombination : Set (𝑖 ､ 𝑗)
    ⟨ Set:PreCombination ⟩ = PreCombination A X
    IHType.hlevel (of Set:PreCombination) = {!!}

    instance
      ISetHom:sort : IHTypeHom Set:PreCombination Set:PreCombination sort
      ISetHom:sort = record {}

    Idempotent:sort : Idempotent (Set:PreCombination)
    ⟨ Idempotent:sort ⟩ = ` sort `
    IIdempotent.idempotent (of Idempotent:sort) = idempotent-sort

instance IIdempotent:sort = #openstruct Idempotent:sort




module _ (A : 𝒰 𝑖) (X : 𝒰 𝑗) {{_ : IAbelian A}} {{_ : IDiscrete A}}
          {{_ : ITotalorder X}} {{_ : IDec-Totalorder X}} where
  Combination = ⟨ Normal (Idempotent:sort A X) ⟩

  Abelian:Combination : Abelian (𝑖 ､ 𝑗)
  ⟨ Abelian:Combination ⟩ = Combination
  IMonoid.𝟷 (IAbelian.AsMult (of Abelian:Combination)) = [] , refl
  IMonoid._⋅_ (IAbelian.AsMult (of Abelian:Combination)) (p , _) (q , _) = ⟨ normalize ⟩ (p ⋅ q)
  IMonoid.assoc-⋅ (IAbelian.AsMult (of Abelian:Combination)) = {!!}
  IMonoid.unit-l-⋅ (IAbelian.AsMult (of Abelian:Combination)) = {!!}
  IMonoid.unit-r-⋅ (IAbelian.AsMult (of Abelian:Combination)) = {!!}

-- TODO: replace the normalize by a direct proof that negating doesn't change the fact of being sorted
  (IAbelian.AsMultInv (of Abelian:Combination) IMonoid:WithInverse.⁻¹-Monoid) (p , _) = ⟨ normalize ⟩ (negate p)




module _ (A : 𝒰 𝑖) (X : 𝒰 𝑗) {{_ : IRing A}} {{_ : IDiscrete A}}
            {{_ : ITotalorder X}} {{_ : IDec-Totalorder X}}
            {{_ : IMonoid X}}
            where
  private
    -- The type of summands
    S = A ×-𝒰 X

    scale : S -> PreCombination A X -> PreCombination A X
    scale (a , x) p = map f p
      where f : S -> S
            f (a₂ , x₂) =  (a ⋅ a₂ , x ⋅ x₂)

    multiply : PreCombination A X -> PreCombination A X -> PreCombination A X
    multiply [] q = []
    multiply (x ∷ p) q = (scale x q) ++-List (multiply p q)


  Monoid:Combination : Monoid (𝑖 ､ 𝑗)
  ⟨ Monoid:Combination ⟩ = Combination A X
  IMonoid.𝟷 (of Monoid:Combination) = ⟨ normalize ⟩ ` 𝟷 , 𝟷 `
  IMonoid._⋅_ (of Monoid:Combination) (p , _) (q , _) = ⟨ normalize ⟩ (multiply p q)
  IMonoid.assoc-⋅ (of Monoid:Combination) = {!!}
  IMonoid.unit-l-⋅ (of Monoid:Combination) = {!!}
  IMonoid.unit-r-⋅ (of Monoid:Combination) = {!!}


  Ring:Combination : Ring (𝑖 ､ 𝑗)
  ⟨ Ring:Combination ⟩ = Combination A X
  IRing.Multiplicative (of Ring:Combination) = of Monoid:Combination
  IRing.Additive (of Ring:Combination) = of Abelian:Combination A X


instance IAbelian:Combination = #openstruct Abelian:Combination
instance IMonoid:Combination = #openstruct Monoid:Combination
instance IRing:Combination = #openstruct Ring:Combination


-- X : 𝒰 ℓ₀
-- X = `𝟙`

-- postulate
--   pp : PreCombination ℤ X


-- mygo : PreCombination ℤ X
-- mygo = f pp









