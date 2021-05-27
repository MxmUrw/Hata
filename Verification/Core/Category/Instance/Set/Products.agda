

module Verification.Core.Category.Instance.Set.Products where

open import Verification.Conventions
open import Verification.Core.Category.Definition
open import Verification.Core.Category.Instance.Functor
open import Verification.Core.Category.Functor.Adjunction
open import Verification.Core.Category.Limit.Kan.Definition
open import Verification.Core.Category.Limit.Kan.Terminal
open import Verification.Core.Category.Limit.Kan.Equalizer
-- open import Verification.Core.Category.Limit.Definition
-- open import Verification.Core.Category.Limit.Product
-- open import Verification.Core.Category.Limit.Equalizer
-- open import Verification.Core.Category.Monad
open import Verification.Core.Category.Instance.Type
open import Verification.Core.Category.Instance.Cat
open import Verification.Core.Category.Instance.SmallCategories
open import Verification.Core.Category.FreeCategory
open import Verification.Core.Category.Quiver
open import Verification.Core.Category.Instance.Set.Definition
open import Verification.Core.Category.Lift
open import Verification.Core.Homotopy.Level


--------------------------------------------------------------------
-- Products

-- A : Set 𝑖

-- (Category:Set 𝑖)
-- (⩚ Set 𝑖)

-- f : X -> X -> Y

-- f : (Bool -> X) -> (⊤ -> X)
--       ≡ X ^ 2        ≡ X ^ 1

-- Geht nicht
-- ** : ∀{A B X : 𝒰 𝑖} -> (f : A -> B) -> (B -> X) -> (A -> X)
-- ** f g = λ x -> g (f x)


-- p : a ≡ b
-- p (i) = ?

-- p : I -> A
-- p (i0) ----> a
-- p (i1) ----> b


_×-Set_ : Set 𝑖 -> Set 𝑗 -> Set (𝑖 ､ 𝑗)
⟨ A ×-Set B ⟩ = ⟨ A ⟩ ×-𝒰 ⟨ B ⟩
IHType.hlevel (of (A ×-Set B)) x y p q =
  let p1 = cong fst p -- : x1 ≡ y1
      p2 = cong snd p -- : x2 ≡ y2
      q1 = cong fst q
      q2 = cong snd q

      P1 : p1 ≡ q1
      P1 = hlevel {{of A}} (fst x) (fst y) p1 q1

      P2 : p2 ≡ q2
      P2 = hlevel {{of B}} (snd x) (snd y) p2 q2

      P : (λ i -> (p1 i , p2 i)) ≡ (λ i -> (q1 i , q2 i))
      P = λ i -> (λ j -> P1 i j , P2 i j)
  in P

module _ where
  private
    L : Functor (⩚ (`𝟚` ⟶ ⩚ Set 𝑖 )) (⩚ (𝟙 ⟶ ⩚ Set 𝑖)) --Fun[ ⩚ 𝟙 , ⩚ 𝒰 𝑖 ]
    ⟨ L ⟩ z = free-Diagram-Lift d
      where d : QuiverHom (` 𝟙-𝒰 `) (ForgetCategory (⩚ Set _))
            ⟨ d ⟩ _ = ⟨ z ⟩ (↥ ₀) ×-Set ⟨ z ⟩ (↥ ₁)
            -- QuiverHom.qmap d ()
    IFunctor.map (of L) α = free-Diagram-Nat f fp
      where f = λ {_ -> ′ (λ {(x , y) -> ⟨ ⟨ α ⟩ ⟩ x , ⟨ ⟨ α ⟩ ⟩ y}) ′ }
            fp = λ {()}
    IFunctor.functoriality-id (of L) x _ = refl
    IFunctor.functoriality-◆ (of L) x _ = refl
    IFunctor.functoriality-≣ (of L) p x (a , b) i = (p (↥ ₀) a i , p (↥ ₁) b i)


    lem::1 : (! `𝟚` *) ⊣ L {𝑖 = 𝑖}
    ⟨ IAdjoint.embed lem::1 ⟩ = free-Diagram-Nat f fp
      where f = λ _ -> ′ (λ {a -> (a , a)}) ′
            fp = λ {()}
    INatural.naturality (of IAdjoint.embed lem::1) α x _ = refl
    ⟨ IAdjoint.eval lem::1 ⟩ = free-Diagram-Nat f (λ {()})
      where f = λ { ₀ -> ′ (λ {(v , w) -> v}) ′
                  ; ₁ -> ′ (λ {(v , w) -> w})′ }
    INatural.naturality (of IAdjoint.eval lem::1) f (↥ ₀) _ = refl
    INatural.naturality (of IAdjoint.eval lem::1) f (↥ ₁) _ = refl
    IAdjoint.reduce-Adj-β lem::1 (↥ ₀) _ = refl
    IAdjoint.reduce-Adj-β lem::1 (↥ ₁) _ = refl
    IAdjoint.reduce-Adj-η lem::1 _ _ = refl

  instance
    hasProducts:Set : has(`𝟚`)ShapedLimits (⩚ Set 𝑖)
    ⟨ hasProducts:Set ⟩ = L
    of hasProducts:Set = lem::1
    -- fst hasProducts:Set = L
    -- snd hasProducts:Set = lem::1


instance
  Terminal:Set : Terminal (` Set 𝑖 `)
  ⟨ ⟨ Terminal:Set ⟩ ⟩ = Lift 𝟙-𝒰
  of ⟨ Terminal:Set ⟩ = {!!}
  ⟨ ITerminal.! (of Terminal:Set) _ ⟩ _ = lift tt
  of ITerminal.! (of Terminal:Set) _ = record {}
  ITerminal.unique (of Terminal:Set) = {!!}

