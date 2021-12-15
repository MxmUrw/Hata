
module Verification.Core.Theory.Std.Specific.FirstOrderTerm.Unification.Introduction where

-- | Unification of terms is important in many kinds of settings related to
--   solving of equations. Our motivation is the unification of free first order terms,
--   as required for Hindley-Milner type inference, but other applications
--   include higher order unification of terms with bound variables or unification
--   of terms over an equational theory. This makes it very appealing to create
--   an axiomatic framework for this problem \cite{UnifyCat:SchmidtSiekmann:1988}.
--
-- | Category theory --- very successful as a language for abstraction REF ---
--   seems like a good candidate. Even very decidedly so since it was noticed
--   that the goal of a unification algorithm, a most general unifier (mgu) of two terms,
--   is the same as a coequalizer of the terms, considered as arrows in the category
--   of term substitutions \cite{UnifyCat:RydeheardBurstall:1986} [fn:: The authors
--   say that this fact was actually brought to their attention by Goguen, who later
--   also published on that topic \cite{UnifyCat:Goguen:1989}.]. One might remark that
--   this happened rather late after both the concepts of unification \cite{Unify:Robinson:1965}
--   and of the category of terms and substitutions REF:Kleisli, REF:Lawvere were introduced
--   \cite{UnifyCat:EGMOV:2002}.
--
-- | Many authors (e.g. \cite{UnifyForm:MannaWaldinger:1981}, \cite{UnifyForm:Paulson:1985}, \cite{UnifyForm:Bove:1999}, \cite{UnifyForm:McBride:2000}) of formal verifications of a unification algorithm note the
--   undesired complexity of their accompanying correctness proofs. Thus, it is perhaps
--   unsurprising that most formalizations do not add further complexities by
--   considering this problem in an abstract categorical context.
--
-- | But additional complexity is not the only possible result when employing
--   category theory: In his thesis, \citet{UnifyForm:McBride:2000} proves a
--   purely categorical and rather elegant lemma: it explains why the recursion step of the
--   algorithm, where a large equation is split into smaller parts which are then solved
--   individually, is correct. This lemma, which McBride calls "the optimist's lemma",
--   is also used in the formalization of higher order unification in Agda by \citet{UnifyCat:VezzosiAbel:2014}.
--   Here, the explicit goal of the authors is to recognize categorical aspects
--   of (higher order) unification, and the treatment of mgu's as coequalizers is
--   explicit. [fn:: In the paper, they are rather defined as equalizers, but this
--   is merely a matter of conventions. The same discrepancy exists
--   between \cite{UnifyCat:RydeheardBurstall:1986} and \cite{UnifyCat:Goguen:1989}.]
-- | Even though in these two formalizations (parts of) the results are stated for
--   general categories, the main computation of a unifier is still done
--   only in some concrete category of terms.
-- | The possibility of a generic unification algorithm and method of formal verification
--   thereof is implied by the existing literature. Nevertheless, it seems that currently
--   this has not been actually done. In this chapter we present such an algorithm.




-- ==* Categorical unification
-- | The underlying algorithm is the same as ...
--
-- | Other applications of the Rydeheard-Burstall approach are
--   to be found in \cite{UnifyCat:EGMOV:2002}, where generalized terms
--   (elements of term powersets) are unified.
-- | \citet{UnifyCat:SchmidtSiekmann:1988} modify the approach to re-include
--    variables in order to attain an algorithm without unnecessary renaming steps.
--    But this requires their theory to move away from the conventional categorical
--    framework given in \cite{UnifyCat:RydeheardBurstall:1986}.
-- | \medskip
--
-- | TODO: Speak about performance of my algorithm.
--



