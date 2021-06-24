
module Verification.Experimental.Theory.Std.LogicalTheory.Definition where

open import Verification.Experimental.Conventions hiding (Structure ; Σ)
open import Verification.Experimental.Category.Std.Category.Definition
open import Verification.Experimental.Category.Std.Functor.Definition
open import Verification.Experimental.Category.Std.Category.Subcategory.Full2
-- open import Verification.Experimental.Category.Std.Graph.Definition
open import Verification.Experimental.Set.Setoid.Definition
-- open import Verification.Experimental.Set.Discrete
-- open import Verification.Experimental.Set.Decidable
open import Verification.Experimental.Data.Universe.Everything


-------------------------------------------------------------------
-- ==* Theories and models
----------------------------------------------------
-- ===* Possible extensions of the current concept
-- | The usual adjunction postulating the syntactical category of, e.g. lambda calculus
--   is:
--
-- |> $ % https://q.uiver.app/?q=WzAsMixbMCwwLCJcXFNpZ21hIl0sWzIsMCwiXFxtYXRoc2Nye019Il0sWzAsMSwiXFx0ZXh0e0ZyZWV9IiwwLHsiY3VydmUiOi0yfV0sWzEsMCwiXFx0ZXh0e0ZvcmdldH0iLDAseyJjdXJ2ZSI6LTJ9XSxbMiwzLCIiLDAseyJsZXZlbCI6MSwic3R5bGUiOnsibmFtZSI6ImFkanVuY3Rpb24ifX1dXQ==
-- \[\begin{tikzcd}
--  \Sigma && {\mathscr{M}}
--  \arrow[""{name=0, anchor=center, inner sep=0}, "{\text{Free}}", curve={height=-12pt}, from=1-1, to=1-3]
--  \arrow[""{name=1, anchor=center, inner sep=0}, "{\text{Forget}}", curve={height=-12pt}, from=1-3, to=1-1]
--  \arrow["\dashv"{anchor=center, rotate=-90}, draw=none, from=0, to=1]
-- \end{tikzcd}\] $


-- | But in the case of actual constructions of free term models one should be able to extend
--   those to another adjunction with the category of sheaves on |Σ|.

-- |> $ % https://q.uiver.app/?q=WzAsMixbMCwwLCJcXHRleHR7U2h9KFxcU2lnbWEpIl0sWzIsMCwiXFxtYXRoc2Nye019Il0sWzAsMSwiXFx0ZXh0e1Rlcm19IiwwLHsiY3VydmUiOi0yfV0sWzEsMCwiXFx0ZXh0e2lzU3RydWN0dXJlfSIsMCx7ImN1cnZlIjotMn1dLFsyLDMsIiIsMCx7ImxldmVsIjoxLCJzdHlsZSI6eyJuYW1lIjoiYWRqdW5jdGlvbiJ9fV1d
-- \[\begin{tikzcd}
--  {\text{Sh}(\Sigma)} && {\mathscr{M}}
--  \arrow[""{name=0, anchor=center, inner sep=0}, "{\text{Term}}", curve={height=-12pt}, from=1-1, to=1-3]
--  \arrow[""{name=1, anchor=center, inner sep=0}, "{\text{isStructure}}", curve={height=-12pt}, from=1-3, to=1-1]
--  \arrow["\dashv"{anchor=center, rotate=-90}, draw=none, from=0, to=1]
-- \end{tikzcd}\] $

-- |> Interestingly, nominal sets [fn:: \href{https://ncatlab.org/nlab/show/nominal+set}{See here.}]
--   are also a sheaf category where |Σ = Fin𝐒𝐞𝐭|. But we do not go into
--   this possible extension to sheaves.

----------------------------------------------------
-- ===* Current concept
-- | Instead we define what a /logical framework/ is using the same data
--   and language of adjunctions, but without actually requiring it
--   to be an adjunction. This is useful in our case since we also want
--   to speak about logical frameworks such as the |MetaTermCalculus|
--   which do generate cartesian categories but are not the initial
--   among their models.


-- [Definition]
-- | Let |ℳ| and |Σ| be categories. We say that |Σ| is a *logical framework* for |ℳ|,
--   i.e., we define the record type [...] as follows:
record isLogicalFramework (ℳ : Category 𝑖) (Σ : Category 𝑗) : 𝒰 (𝑖 ⁺ ､ 𝑗 ⁺) where

  -- |: 1. We require two functions
  field Free : ⟨ Σ ⟩ -> ⟨ ℳ ⟩
  field Forget : ⟨ ℳ ⟩ -> ⟨ Σ ⟩

  -- | 2. Both have to be functors
  field {{isFunctor:Free}} : isFunctor Σ ℳ Free
  field {{isFunctor:Forget}} : isFunctor ℳ Σ Forget

  -- | 3. And finally we want a map which shows that every |σ| structure
  --      is a model of |Free Σ|
  field ⟦_⟧ : ∀{σ m} -> (σ ⟶ Forget m) -> (Free σ ⟶ m)

  -- |: 1. Here we should end... And this?

-- //





  -- -- - We define the structure 
  -- Structure : Σ -> 𝒰 _
  -- Structure σ = ∑ isStructure σ

  -- instance
  --   StructureCat : ∀ {σ} -> isCategory _ (Structure σ)
  --   StructureCat = isCategory:FullSubcategory (fst)

  -- field Term : (σ : Σ) -> ⟨ ℳ ⟩
  -- field ⟦_⟧ : ∀{σ} -> {A : ⟨ ℳ ⟩} -> isStructure σ A -> (Term σ) ⟶ A
  -- field makeStr : ∀{σ A} -> (Term σ) ⟶ A -> isStructure σ A

  -- field isInitial:Term : ∀{σ} -> isInitial (Term σ)


