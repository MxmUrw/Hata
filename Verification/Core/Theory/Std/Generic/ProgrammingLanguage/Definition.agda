
module Verification.Core.Theory.Std.Generic.ProgrammingLanguage.Definition where

open import Verification.Core.Conventions
open import Verification.Core.Set.Setoid.Definition
open import Verification.Core.Set.Discrete
open import Verification.Core.Set.Decidable
open import Verification.Core.Data.Universe.Definition
open import Verification.Core.Data.Universe.Instance.Category
open import Verification.Core.Data.Universe.Instance.Category
open import Verification.Core.Data.Prop.Everything
open import Verification.Core.Data.Sum.Definition
-- open import Verification.Core.Data.Rational.Definition
-- open import Verification.Core.Algebra.Monoid.Definition
-- open import Verification.Core.Category.Std.Category.Definition
-- open import Verification.Core.Theory.Computation.Question.Definition
-- open import Verification.Core.Category.Std.Morphism.Iso
-- open import Verification.Core.Theory.Computation.Question.Construction.Product

open import Verification.Core.Theory.Std.Generic.TypeTheory.Definition
open import Verification.Core.Theory.Std.Generic.Theory.Definition
open import Verification.Core.Theory.Std.Generic.ComputationalTheory.Definition

open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Category.Std.Category.Subcategory.Full
open import Verification.Core.Category.Std.Graph.Definition

open import Verification.Core.Category.Std.Fibration.Specific.Fam.Definition
open import Verification.Core.Category.Std.Fibration.BaseChange.Definition
open import Verification.Core.Category.Std.Fibration.Definition
open import Verification.Core.Category.Std.Fibration.Instance.BaseChange

open import Verification.Core.Computation.Question.Definition
open import Verification.Core.Computation.Question.Specific.Check


open import Verification.Application.Definition

-- {𝑖 : 𝔏 ×-𝒰 𝔏 ×-𝒰 𝔏 ×-𝒰 𝔏} →
-- TypeTheory 𝑖 →
-- Theory
-- (fst 𝑖 , ℓ-max (fst (snd 𝑖)) (snd (snd (snd 𝑖))) , fst (snd 𝑖))


private macro
  U = instance[ "" , 𝑖 ] (TypeTheory 𝑖 -> Theory _) ◀
  F2 = instance[ "" , 𝑖 ] (𝐓𝐓 𝑖 -> Theory _) ◀
  F3 = instance[ "" , 𝑖 ] (Computational 𝑖 -> Theory _) ◀
  gstd = instance[ "" , 𝑖 ] (Graph 𝑖 -> Setoid _) ◀


record isLanguage (𝑖 : 𝔏 ^ 3) (Type : 𝒰 𝑗) : 𝒰 (𝑖 ⁺ ､ 𝑗 ⁺) where
  constructor language
  field Termᵘ-PL : 𝒰 (𝑖 ⌄ 0)

  field _∶-PL_ : Termᵘ-PL -> Type -> 𝒰 (𝑖 ⌄ 2)

  TypedTermᵘ-PL : Type -> 𝒰 _
  TypedTermᵘ-PL τ = (∑ λ (t : Termᵘ-PL) -> t ∶-PL τ)

  field {{isGraph:Termᵘ-PL}} : isGraph {𝑖 ⌄ 1} (Termᵘ-PL)

  field preserveType-PL : ∀ {t₁ t₂} -> (Edge t₁ t₂) -> ∀{τ : Type} -> t₁ ∶-PL τ -> t₂ ∶-PL τ

  macro Term-PL = #structureOn Termᵘ-PL

  -- instance
  --   isSetoid:TypedTerm-PL : ∀{τ} -> isSetoid _ (TypedTermᵘ-PL τ)
  --   isSetoid:TypedTerm-PL = {!!}

  isSetoid:Term-PL : isSetoid (Term-PL)
  isSetoid:Term-PL = isSetoid:FullSubsetoid (gstd Term-PL) (incl)

open isLanguage {{...}} public


module _ (𝑖 : 𝔏 ^ 4) where
  Language = 𝒰 (𝑖 ⌄ 0) :& isLanguage (𝑖 ⌄ 1 ⋯ 3)
  macro 𝐋𝐚𝐧𝐠 = #structureOn (Language)

private
  Forget : 𝐋𝐚𝐧𝐠 𝑖 -> 𝐓𝐓 _
  Forget 𝓛 = ⟨ 𝓛 ⟩ since typeTheory Term-PL {{isSetoid:Term-PL}} _∶-PL_ {!!}

private macro
  p = instance[ "" , 𝑖 / 3 ] (𝐅𝐚𝐦 (𝐐𝐮𝐞𝐬𝐭 (𝑖 ⌄ 0 ⋯ 1)) (𝑖 ⌄ 2) -> 𝐓𝐲𝐩𝐞 _) ◀

-- LangFib : Fiber p (𝐋𝐚𝐧𝐠 𝑖)
-- LangFib {𝑖} = ⟨ (Forget {𝑖}) *! ⟩ (𝐓𝐓Fib _)

record LanguageClass (𝑖 : 𝔏 ^ 4) : 𝒰 (𝑖 ⁺ ⁺) where
  constructor languageClass
  field Name : String
  field Param : 𝒰 ((⨆ 𝑖) ⁺)
  field Lang : Param -> 𝐋𝐚𝐧𝐠 𝑖

open LanguageClass public

instance
  hasU:LanguageClass : hasU (LanguageClass 𝑖) _ _
  hasU:LanguageClass = hasU:Base _


module _ {𝑖} where
  record isImplemented (𝓛 : LanguageClass 𝑖) : 𝒰 (𝑖 ⁺ ⁺) where
    constructor isimplemented
    -- field implementation : Solution LangFib (𝓛 .Lang)

  ImplementedLanguageClass = _ :& isImplemented

languageApplication : (𝓛 : ImplementedLanguageClass {𝑖}) -> Application
languageApplication 𝓛 = execute ("check-" <> name) checkE
  where
    name = ⟨ 𝓛 ⟩ .Name

    checkE : String -> Printable
    checkE str = PString "Executing this language is currently not implemented."







-- Language = F1 ◰ F2

--------------------------------------------------------------------
-- A programming language is a type theory with solved checking problem
-- and a computational model

{-
record isLanguage 𝑗 (𝓣 : TypeTheory 𝑖) : 𝒰 (𝑖 ⁺ ､ 𝑗 ⁺) where
  field {{Comp}} : isComputational 𝑗 (ttheo 𝓣)
  field Input : Canonical {{Comp}}
  field Output : Canonical {{Comp}}
  field check : ∀ (t : ⟨ Term ⟩) -> isDecidable (t ∶ Input ⇛ Output)

open isLanguage {{...}} public

Language : (𝑖 : 𝔏 ^ 6) -> 𝒰 _
Language 𝑖 = TypeTheory (𝑖 ⌄ 0 , 𝑖 ⌄ 1 , 𝑖 ⌄ 2 , 𝑖 ⌄ 3) :& isLanguage (𝑖 ⌄ 4 , 𝑖 ⌄ 5)

-- Computational 𝑖 = Theory 

-- record Language 𝑖 𝑗 : 𝒰 (𝑖 ⁺ ､ 𝑗 ⁺) where
--   field 𝓣 : TypeTheory 𝑖
--   field {{Comp}} : isComputational 𝑗 (ttheo 𝓣)
--   field Input : Canonical {{Comp}}
--   field Output : Canonical {{Comp}}
--   field check : ∀ (t : ⟨ Term ⟩) -> isDecidable (t ∶ Input ⇛ Output)


record Interpreter (𝓟 : Language 𝑖) : 𝒰 (𝑖 ⁺) where
  field Error : 𝒰₀
  field typeerror : Error
  field parse : String -> Error + ⟨ Term ⟩
  field parseInput : String -> Error + ((Input .fst) ■N)
  field printOutput : (Output .fst) ■N -> String

open Interpreter

interpretProgram : {𝓟 : Language 𝑖} (I : Interpreter 𝓟) -> (program : String) -> (input : String) -> (I .Error) + String
interpretProgram I program input =
  case (parseInput I input) of
    left
    λ i -> case (parse I program) of
            left
            λ p -> case check p of
              (const (left (typeerror I)))
              λ τ → right (printOutput I (run (p , τ) i))

-}
