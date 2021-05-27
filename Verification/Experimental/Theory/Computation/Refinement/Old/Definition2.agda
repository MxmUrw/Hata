
-- {-# OPTIONS --type-in-type #-}

module Verification.Experimental.Theory.Computation.Problem.Definition2 where

open import Verification.Experimental.Conventions
open import Verification.Experimental.Set.Setoid.Definition
open import Verification.Experimental.Data.Universe.Everything
open import Verification.Experimental.Data.Prop.Everything
open import Verification.Experimental.Order.WellFounded.Definition
open import Verification.Experimental.Category.Std.Category.Definition


---------------------------------------------------------------
-- Definition of a problem

record isProblem (𝑖 : 𝔏) (A : 𝒰 𝑗) : 𝒰 (𝑖 ⁺ ､ 𝑗 ⁺ ⁺) where
  field Property : (A -> 𝒰 𝑗) -> 𝒰 (𝑗 ⁺)
  field Solution : ∀(P : A -> 𝒰 𝑗) -> (Property P) -> (a : A) -> P a -> 𝒰 𝑖


open isProblem {{...}} public

Problem : (𝑖 : 𝔏 ^ 2) -> 𝒰 _
Problem 𝑖 = 𝒰 (𝑖 ⌄ 0) :& isProblem (𝑖 ⌄ 1)

---------------------------------------------------------------
-- An important object in this category is the "solved" object
record Solved : 𝒰₀ where

instance
  isProblem:Solved : isProblem _ Solved
  isProblem:Solved = record
    { Property = const ⊤-𝒰
    ; Solution = λ P x a x₁ → 𝟙-𝒰
    }

  -- record { SolutionSpace = λ _ -> 𝟙-𝒰 }

---------------------------------------------------------------
-- Definition of reductions


module _ (A : Problem (𝑖 , 𝑗)) (B : Problem (𝑖 , 𝑘)) where
  record isReduction (f : ⟨ A ⟩ -> ⟨ B ⟩) : 𝒰 (𝑖 ⁺) where
    field propMap : ∀(P : ⟨ B ⟩ -> _) -> Property P -> (Property (P ∣ f))
    -- field solutionMap : ∀{P : ⟨ A ⟩ -> 𝒰 _} -> 
    -- SolutionSpace a ↔ SolutionSpace (f a)

  open isReduction {{...}} public

  Reduction : 𝒰 _
  Reduction = _ :& isReduction

-- this forms a category

{-
instance
  isCategory:Problem : isCategory (_ , 𝑖 ⌄ 0) (Problem 𝑖)
  isCategory:Problem =
    record
    { Hom'         = Reduction
    ; isSetoid:Hom = {!!}
    ; id           = {!!}
    ; _◆_          = {!!}
    ; unit-l-◆   = {!!}
    ; unit-r-◆   = {!!}
    ; unit-2-◆   = {!!}
    ; assoc-l-◆  = {!!}
    ; assoc-r-◆  = {!!}
    ; _◈_        = {!!}
    }



---------------------------------------------------------------
-- A problem is solved if it has a hom to Solved

hasSolutions : Problem 𝑖 -> 𝒰 _
hasSolutions Π = ∀(p : ⟨ Π ⟩) -> SolutionSpace p

private
  lem-10 : ∀{Π : Problem 𝑖} -> hasSolutions Π ↔ (Reduction Π ′(Solved)′)
  lem-10 {Π = Π} =
    let f : hasSolutions Π -> (Reduction Π ′(Solved)′)
        f x = ′ (λ x₁ → record {}) ′ {{record { sameSolution = (λ x₁ → tt) , λ x₁ → x _ }}}
        g : (Reduction Π ′(Solved)′) -> hasSolutions Π
        g = λ x p → sameSolution .snd tt
    in f , g

-}

---------------------------------------------------------------
-- Every problem can be turned into the problem of
-- finding a divide and conquer solution

record DivideAndConquer (Π : Problem 𝑖) : 𝒰 (𝑖 ⌄ 0) where
  field original : ⟨ Π ⟩
open DivideAndConquer {{...}} public

postulate
  cU : ∀{𝑖 𝑗} -> 𝒰 𝑖 -> 𝒰 𝑗

record DivideAndConquerProp (Π : Problem 𝑖) (P : DivideAndConquer Π -> 𝒰 (𝑖 ⌄ 0)) : 𝒰 ((fst 𝑖) ⁺) where
  field Size : WFT (ℓ₀ , ℓ₀)
  field size : (∑ P) -> ⟨ Size ⟩
  field originalP : Property {{of Π}} (λ x -> (P (record {original = x})))
  -- field ∂ : ⟨ Π ⟩ -> ∑ λ n -> Fin-R n -> ⟨ Π ⟩
  -- field size-∂ : ∀ p -> ∀ i -> size (∂ p .snd i) ≪ size p

open DivideAndConquerProp {{...}} public

-- record DivideAndConquerSolution {Π : Problem 𝑖} (P : DivideAndConquer Π) : 𝒰 𝑖 where
--   field ∂-solves : ∀ (p : ⟨ Π ⟩) -> (∀ i -> SolutionSpace (∂ {{P}} p .snd i)) -> SolutionSpace p

𝖣𝖺𝖢 : ∀ (Π : Problem 𝑖) -> SomeStructure
𝖣𝖺𝖢 Π = structureOn (DivideAndConquer Π)

module _ {Π : Problem 𝑖} where
  instance
    isProblem:𝖣𝖺𝖢 : isProblem (𝑖 ⌄ 1) (𝖣𝖺𝖢 Π)
    isProblem:𝖣𝖺𝖢 = record
      { Property = DivideAndConquerProp Π
      ; Solution = {!!}
      }
    -- record { SolutionSpace = DivideAndConquerSolution }

dac : Problem 𝑖 -> Problem _
dac Π = 𝖣𝖺𝖢 Π

fmap-dac : ∀{Ω Π : Problem 𝑖} -> (f : Reduction Ω Π) -> 𝖣𝖺𝖢 Ω -> 𝖣𝖺𝖢 Π
fmap-dac f x = record { original = ⟨ f ⟩ (x .original) }

instance
  isReduction:fmap-dac : ∀{Ω Π : Problem 𝑖} -> {f : Reduction Ω Π} -> isReduction (𝖣𝖺𝖢 Ω) (𝖣𝖺𝖢 Π) (fmap-dac f)
  isReduction:fmap-dac {f = f} = record
    { propMap = λ P x → record
                         { Size = x .Size
                         ; size = λ y → let f = x .size
                                        in f (_ , y .snd)
                         ; originalP = let Q = x .originalP
                                           xx = propMap {{of f}} _ Q
                                       in xx
                         }
    }

module _ {Π : Problem 𝑖} where
  η-𝖣𝖺𝖢 : ⟨ Π ⟩ -> 𝖣𝖺𝖢 Π
  η-𝖣𝖺𝖢 x = record { original = x }

  instance
    isReduction:η-𝖣𝖺𝖢 : isReduction Π (𝖣𝖺𝖢 Π) η-𝖣𝖺𝖢
    isReduction:η-𝖣𝖺𝖢 = record
      { propMap = λ P x → let Q = originalP {{x}}
                          in Q
      }

{-
{-
  record
  { original = ⟨ f ⟩ (x .original)
  ; Size = {!!}
  ; size = {!!}
  ; ∂ = {!!}
  ; size-∂ = {!!}
  }

  η-𝖣𝖺𝖢 : 𝖣𝖺𝖢 Π -> ⟨ Π ⟩
  η-𝖣𝖺𝖢 x = x .original


  instance
    isReduction:η-𝖣𝖺𝖢 : isReduction (𝖣𝖺𝖢 Π) Π η-𝖣𝖺𝖢
    isReduction:η-𝖣𝖺𝖢 = record { sameSolution = {!!} }

  μ-𝖣𝖺𝖢 : 𝖣𝖺𝖢 Π -> (𝖣𝖺𝖢 (𝖣𝖺𝖢 Π))
  μ-𝖣𝖺𝖢 P =
    record
    { original = P
    ; Size = P .Size
    ; size = λ s → size {{P}} (s .original)
    ; ∂ = {!!}
    ; size-∂ = {!!}
    }

-- F分 : Problem 𝑖 -> 


{-
record Problem (𝑖 : 𝔏 ^ 3) : 𝒰 (𝑖 ⁺) where
  field Param : 𝒰 (𝑖 ⌄ 0)
  field Idx : Param -> 𝒰 (𝑖 ⌄ 1)
  field SolutionSpace : ∀{p} -> Idx p -> 𝒰 (𝑖 ⌄ 2)

open Problem public

record Solution (Π : Problem 𝑖) : 𝒰 𝑖 where
  field solution : ∀{p} -> (i : Idx Π p) -> SolutionSpace Π i

open Solution public



module _ (Ω : Problem 𝑖) (Π : Problem 𝑗) where
  record Reduction : 𝒰 (𝑖 ､ 𝑗) where
    field rParam : Param Ω -> Param Π
    field rIdx : ∀{p} -> Idx Ω p -> Idx Π (rParam p)
    field rSolution : ∀{p} -> ∀(i : Idx Ω p) -> (SolutionSpace Ω i ↔ SolutionSpace Π (rIdx i))
  open Reduction public

module _ {Ω : Problem 𝑖} {Π : Problem 𝑗} where
  reduce : (Reduction Ω Π) -> (Solution Π -> Solution Ω)
  reduce r s = record { solution = λ i → rSolution r i .snd (solution s (rIdx r i)) }


-- DaC
-- 分 Π -> 分 Ω

-- η : 分 Π ⟶ Π
-- μ : 分 Π ⟶ 分 (分 Π)

-- 赤


-- I can reduce every problem to the problem of finding a reductive solution

module Reductive (Π : Problem 𝑖) where
  Param-分 : 𝒰 _
  Param-分 = Param Π


  -- record ReductiveSolutionSpace : 𝒰 (𝑖 ⁺) where
  --   field Size : 𝒰₀
  --   field size : Idx Π 
  -}

-}
-}
