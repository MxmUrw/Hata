
module Verification.Explorational.Complexity.Axiomatic where

open import Verification.Conventions hiding (Path) public
open import Verification.Experimental.Data.Prop.Everything
open import Verification.Experimental.Category.Std.Graph.Definition public


RewritingSystem : 𝒰 𝑖 -> _
RewritingSystem {𝑖} A = isGraph {𝑖} A

record Problem (A : 𝒰 𝑖) : 𝒰 (𝑖 ⁺) where
  constructor problem
  field Question : 𝒫 A
  field Answer  : 𝒫 A
  field solve : ⦋ Question ⦌ -> ⦋ Answer ⦌



module _ {A : 𝒰 𝑖} where
  _⇝[_]_ : A -> RewritingSystem A -> A -> 𝒰 _
  _⇝[_]_ a ψ b = Edge {{ψ}} a b

  data Path (ψ : RewritingSystem A) : (n : ℕ) -> (a b : A) -> 𝒰 𝑖 where
    [] : ∀{a} -> Path ψ 0 a a
    _,,_ : ∀{a b c} -> Path ψ n a b -> b ⇝[ ψ ] c -> Path ψ (suc n) a c

  syntax Path ψ n a b = a ⇝[ ψ ∣ n ] b

  module _ (ψ : RewritingSystem A) where

  -- we have a solution mapper `any` : 𝒫 Answer -> 𝒫_singleton Answer

  -- We say that ψ `any`-solves a problem (Π,f) if for the set of visited S_x = {a : A | x ⇝[ ψ ] a}
  -- we have any (S_x) ∼ singl (f x)

  -- we can now define standard properties of problems by saying that
  -- - if ψ solves (Π,f), then Π is 𝒰-`any`-semidecidable
  -- - if additionally, every branch of ψ is [n] sized for some n, then
  --   Π is [n]-`any`-semidecidable. This should be the standard notion of semi-decidable
  -- - this is equivalent to [1]-`any`-semidecidable.
  -- - we say that ψ decides Π if every branch of ψ lands in Answer. Then Π is also ?-`any`-decidable
  -- - we have that [n]-`any`-decidable ≃ [n]-`all`-decidable
  -- - We can now restrict to systems ψ which are decidable (everything terminates) and also
  --   where every branch runs in polynomial time wrt. the necessary time to build the input using
  --   the best possible system ι ∈ Ψ , where Ψ ⊆ RS is the set of allowed rewriting systems, e.g. Turing Machines.
  --   such that (start ⇝[ ι ∣ n ] x). The best such n is the size of the input.
  -- - Then we can say that the class P is given by [1]-`any`-decidable-poly. And is equivalent to [1]-`all`-decidable-poly.
  -- - NP is given by [n]-`any`-decidable-poly
  -- - coNP is given by [n]-`all`-decidable-poly



