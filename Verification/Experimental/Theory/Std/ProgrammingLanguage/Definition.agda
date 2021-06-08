
module Verification.Experimental.Theory.Std.ProgrammingLanguage.Definition where

open import Verification.Experimental.Conventions
open import Verification.Experimental.Set.Setoid.Definition
open import Verification.Experimental.Set.Discrete
open import Verification.Experimental.Set.Decidable
open import Verification.Experimental.Data.Universe.Everything
open import Verification.Experimental.Data.Universe.Instance.Category
open import Verification.Experimental.Data.Prop.Everything
open import Verification.Experimental.Data.Sum.Definition
-- open import Verification.Experimental.Data.Rational.Definition
-- open import Verification.Experimental.Algebra.Monoid.Definition
-- open import Verification.Experimental.Category.Std.Category.Definition
-- open import Verification.Experimental.Theory.Computation.Question.Definition
-- open import Verification.Experimental.Category.Std.Morphism.Iso
-- open import Verification.Experimental.Theory.Computation.Question.Construction.Product

open import Verification.Experimental.Theory.Std.TypeTheory.Definition
open import Verification.Experimental.Theory.Std.Theory.Definition
open import Verification.Experimental.Theory.Std.ComputationalTheory.Definition

open import Verification.Experimental.Category.Std.Category.Definition
open import Verification.Experimental.Category.Std.Category.Subcategory.Full

-- {𝑖 : 𝔏 ×-𝒰 𝔏 ×-𝒰 𝔏 ×-𝒰 𝔏} →
-- TypeTheory 𝑖 →
-- Theory
-- (fst 𝑖 , ℓ-max (fst (snd 𝑖)) (snd (snd (snd 𝑖))) , fst (snd 𝑖))


private macro
  F1 = instance[ "" , 𝑖 ] (TypeTheory 𝑖 -> Theory _) ◀
  F2 = instance[ "" , 𝑖 ] (𝐓𝐓 𝑖 -> Theory _) ◀
  F3 = instance[ "" , 𝑖 ] (Computational 𝑖 -> Theory _) ◀


-- private
--   F1' : Hom {{of 𝐂𝐚𝐭}} _ _
--   F1' = incl F1

-- ProgrammingLanguage = F1 ◰ F2

--------------------------------------------------------------------
-- A programming language is a type theory with solved checking problem
-- and a computational model

{-
record isProgrammingLanguage 𝑗 (𝓣 : TypeTheory 𝑖) : 𝒰 (𝑖 ⁺ ､ 𝑗 ⁺) where
  field {{Comp}} : isComputational 𝑗 (ttheo 𝓣)
  field Input : Canonical {{Comp}}
  field Output : Canonical {{Comp}}
  field check : ∀ (t : ⟨ Term ⟩) -> isDecidable (t ∶ Input ⇛ Output)

open isProgrammingLanguage {{...}} public

ProgrammingLanguage : (𝑖 : 𝔏 ^ 6) -> 𝒰 _
ProgrammingLanguage 𝑖 = TypeTheory (𝑖 ⌄ 0 , 𝑖 ⌄ 1 , 𝑖 ⌄ 2 , 𝑖 ⌄ 3) :& isProgrammingLanguage (𝑖 ⌄ 4 , 𝑖 ⌄ 5)

-- Computational 𝑖 = Theory 

-- record ProgrammingLanguage 𝑖 𝑗 : 𝒰 (𝑖 ⁺ ､ 𝑗 ⁺) where
--   field 𝓣 : TypeTheory 𝑖
--   field {{Comp}} : isComputational 𝑗 (ttheo 𝓣)
--   field Input : Canonical {{Comp}}
--   field Output : Canonical {{Comp}}
--   field check : ∀ (t : ⟨ Term ⟩) -> isDecidable (t ∶ Input ⇛ Output)


record Interpreter (𝓟 : ProgrammingLanguage 𝑖) : 𝒰 (𝑖 ⁺) where
  field Error : 𝒰₀
  field typeerror : Error
  field parse : String -> Error + ⟨ Term ⟩
  field parseInput : String -> Error + ((Input .fst) ■N)
  field printOutput : (Output .fst) ■N -> String

open Interpreter

interpretProgram : {𝓟 : ProgrammingLanguage 𝑖} (I : Interpreter 𝓟) -> (program : String) -> (input : String) -> (I .Error) + String
interpretProgram I program input =
  case (parseInput I input) of
    left
    λ i -> case (parse I program) of
            left
            λ p -> case check p of
              (const (left (typeerror I)))
              λ τ → right (printOutput I (run (p , τ) i))

-}
