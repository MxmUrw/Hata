
module Verification.Core.Computation.Unification.Categorical2.GenericUnification where

-- | The next steps, which are done in the formalization
--   in order to show that |𝐒𝐮𝐛𝐬𝐭-FO| has unification, are briefly
--   sketched here.
-- | - We show that |isEpiPrincipal (CoeqIdeal t s)| is equivalent
--     to the existence of a coequalizer decision for the pair |(t,s)|.
--     The proof works by checking whether the representing morphism
--     is zero or an epi, and constructing either a proof of nonexistence,
--     or a coequalizer, repectively. Similarly in the other direction.
-- | - We formulate a condition for categories with zero morphisms
--     that allows us to show that every ideal given by |(CoeqIdeal t s)|
--     is epi-principal. It requires a well-founded relation, and a
--     way to split ideals into finite conjunctions of ideals.
--     But this proof cannot be used by itself to show existence of coequalizers:
--     For the base case of the induction the existence has to
--     be shown using other methods. It is here that we resort to traditional methods
--     for (the formalization of) unification.
-- | - Finally, using a reformulation of the above condition which is stated
--     for categories without the requirement of zero morphisms, and showing
--     that our category |𝐒𝐮𝐛𝐬𝐭-FO| does fulfill this condition, we get a
--     complete proof that this category has unification.
--



