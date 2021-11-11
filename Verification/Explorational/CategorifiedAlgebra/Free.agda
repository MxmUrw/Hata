
{-# OPTIONS --guardedness #-}

module Verification.Explorational.CategorifiedAlgebra.Free where

open import Verification.Conventions hiding (Path)
open import Verification.Core.Category.Std.Morphism.Iso
open import Verification.Core.Data.AllOf.Universe
open import Verification.Core.Data.AllOf.Product
open import Verification.Core.Data.AllOf.Sum



module _ (F : 𝒰₀ -> 𝒰₀) where

  {-# NO_POSITIVITY_CHECK #-}
  data Free : 𝒰₀ where
    next : F Free -> Free

  {-# NO_POSITIVITY_CHECK #-}
  record CoFree : 𝒰₀ where
    coinductive
    field conext : F CoFree

  open CoFree public


List' : 𝒰₀ -> 𝒰₀
List' X = Free (λ A -> ⊤-𝒰 + (X × A))


module _ {X : 𝒰₀} where
  ϕ : List X -> List' X
  ϕ [] = next nothing
  ϕ (x ∷ xs) = next (right (x , (ϕ xs)))

  ψ : List' X -> List X
  ψ (next (left x)) = []
  ψ (next (just (x , xs))) = x ∷ ψ xs


Equation = 𝒰₀ × 𝒰₀ -> 𝒰₀

Solution : Equation -> 𝒰 _
Solution Eq = ∑ λ (A : 𝒰₀ -> 𝒰₀) -> ∀ X -> A X ≅ Eq (A X , X)


FreeSol : Equation -> (𝒰₀ -> 𝒰₀)
FreeSol Eq X = Free (λ A' -> Eq (A' , X))


CoFreeSol : Equation -> (𝒰₀ -> 𝒰₀)
CoFreeSol Eq X = CoFree (λ A' -> Eq (A' , X))

getSolution : (Eq : Equation) -> Solution Eq
getSolution Eq = A , lem-1
  where
    A : 𝒰₀ -> 𝒰₀
    A = FreeSol Eq
    -- Free (λ A' -> Eq (A' , X)) X
    -- A X = Free (λ A' -> Eq (A' , X)) X

    f : (X : 𝒰₀) → A X -> Eq (A X , X)
    f X (next x) = x

    g : (X : 𝒰₀) → Eq (A X , X) -> A X
    g X e = next e

    lem-1 : (X : 𝒰₀) → A X ≅ Eq (A X , X)
    lem-1 X = f X since record { inverse-◆ = g X ; inv-r-◆ = λ {i (next x) → next x} ; inv-l-◆ = refl }



getSolution2 : (Eq : Equation) -> Solution Eq
getSolution2 Eq = A , lem-1
  where
    A : 𝒰₀ -> 𝒰₀
    A = CoFreeSol Eq
    -- Free (λ A' -> Eq (A' , X)) X
    -- A X = Free (λ A' -> Eq (A' , X)) X

    f : (X : 𝒰₀) → A X -> Eq (A X , X)
    f X a = conext a
    -- X (next x) = x

    g : (X : 𝒰₀) → Eq (A X , X) -> A X
    conext (g X a) = a

    lem-0 : ∀ {X} -> ∀ a -> g X (conext a) ≡ a
    conext (lem-0 a i) = conext a

    lem-1 : (X : 𝒰₀) → A X ≅ Eq (A X , X)
    lem-1 X = f X since record { inverse-◆ = g X ; inv-r-◆ = funExt lem-0 ; inv-l-◆ = refl }


--
-- the initial solution
--

prop-1 : Free (id-𝒰) -> ⊥-𝒰 {ℓ₀}
prop-1 (next x) = prop-1 x

prop-2 : CoFree id-𝒰
conext prop-2 = prop-2




-- If a functor solves the equation Eq, then it is isomorphic to the free solution
-- this is not true!
-- module _ {Eq : Equation} where
--   prop-1 : ∀((F , FP) : Solution Eq) -> ∀ X -> F X ≅ FreeSol Eq X
--   prop-1 (F , FP) X = {!!}
--     where
--       f : F X -> FreeSol Eq X
--       f =
--         let f1 = ⟨ FP X ⟩
--         in λ x → next {!!}


