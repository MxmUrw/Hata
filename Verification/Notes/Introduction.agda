
module Verification.Writing.Introduction where

open import Verification.Conventions hiding (_≟_)
open import Verification.Unification.Instance.HMType
open import Verification.Writing.Introduction-back

-- = Introduction

-- ==* The goal
-- | The goal of this thesis is to find an algebraic approach to typechecking, in particular to the problem of unification of types.
--   This includes the task to formally verify the correctness of it. In other words, this implies that the product will be a formally verified unifier
--   (and typechecker) for some class of type theories, including Hindley-Milner style lambda-calculus.


-- ==* The idea
-- | The premise for this work is the fact that the process of unification is very similar to the process of solving algebraic equations.
--   Above all, this is to be expected, because in both cases we have to solve for variables, and deal with the resulting substitutions.

-- | An interesting further similarity is that, given two types [..] and [..],
τ₁ = 𝐵 ⇒ (𝐵 ⇒ 𝑁)
τ₂ = 𝐵 ⇒ var ₀

-- |> the question of whether they are unifiable [...,] involves finding those parts of the terms which differ, while forgetting about those parts which are the same.
q₁ = ((𝐵 ⇒ (𝐵 ⇒ 𝑁)) ≟ (𝐵 ⇒ var ₀))
-- |> Thus, what actually needs to be solved is [....] Again, this is almost like in algebra, where we consider |p - q ≡ 0|, and thus cancel equal parts, in order to solve |p ≡ q|.
q₂ = (𝐵 ⇒ 𝑁) ≟ var ₀

-- | The idea is to find an environment where it makes sense to speak about the difference |τ₁ - τ₂| of the two given types.
--   More precisely, we search for a module |M| over some ring into which we can embed the set of types such that:

-- | \begin{enumerate}
--   \item Taking the quotient module $\frac{M}{(τ₁ - τ₂)}$ does the same computation
--     as the unification of |τ₁| and |τ₂|.
--   \item It is possible to extract this information again into
--     substitutions of terms.
--   \end{enumerate}

-- | This allows us to use generic algebraic tools for the actual computation, namely, finding an explicit description of the quotient module together with a normalization procedure.
--   Fortunately, it seems that the procedure of finding a /Groebner basis/ does exactly this.

-- ==* The approach

-- | We plan to make
--   the idea formal by:

-- | \begin{enumerate}
--   \item Noting that terms with free variables form a (free) monad |T|, and unifying terms is equivalently the computation of coequalizers in the Kleisli category |𝒞 ⌄ T|.
--   \item Specifying an additional structure which has to exist on a monad |T|, in order for us to able to construct an associated ring |R ⌄ T|,
--        and give a functor: |F : 𝒞 ⌄ T ⟶ Mod ⌄ (R ⌄ T)|
--   \item Given two maps |f g : a ⟶ b| in |𝒞|, using the computation of Groebner bases to
--         compute the coequalizer of |F f| and |F g| in |Mod ⌄ (R ⌄ T)|.
--   \item Showing how we can lift this computed coequalizer back to |𝒞 ⌄ T|.
--   \end{enumerate}

-- ==* About this document
-- | This document is written using "literate Agda source code". But in order to keep everything more readable (in the pdf, as well as in the original source code),
--   a custom built tool is used, which preprocesses the files and also hooks into Agda's latex generation for post processing.
--   Thus, the code can be annotated using lightweight "docstring"-like syntax, and in the output many details like universe levels are hidden, while e.g. |∏|-types get a
--   more prominent display.



