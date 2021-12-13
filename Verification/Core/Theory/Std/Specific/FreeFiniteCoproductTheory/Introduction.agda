
module Verification.Core.Theory.Std.Specific.FreeFiniteCoproductTheory.Introduction where

-- | In this chapter we define the notion of terms
--   for which we are going to implement the unification algorithm.
--   As the actual difficulty of this implementation
--   does not increase much when comparing "unification for the terms of |Te-Ex|",
--   to "unification for terms over some signature of n-ary function symbols",
--   we opt for the latter. Considered from the point of view
--   of possibly executing this algorithm, this greatly enhances
--   its usability. In fact, we even define them as many sorted terms.
--   Such a definition in the context of categorical
--   unification may be found in \cite{UnifyCat:Goguen:1989}.
--
-- | \medskip
--
-- | We continue by deriving the category of substitutions of such terms
--   as the Kleisli category arising from a monadic structure.
--   This is also standard, similarly to be found in \cite{UnifyCat:Goguen:1989} or REF.
--



