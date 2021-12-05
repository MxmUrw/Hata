
module Verification.Core.Computation.Unification.Definition where

open import Verification.Conventions

open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Category.Std.Limit.Specific.Coequalizer
open import Verification.Core.Set.Decidable

-- | Unification, is the question of whether, given two
--   terms |t s : Term Γ τ| which use the metavariables in |Γ| and
--   are of sort |τ|, there is a substitution |σ| such that |t [σ] ≣ s [σ]|
--   From a categorical point of view we can consider such terms to
--   be arrows |incl τ ⟶ Γ| from the one element list containing |τ| to |Γ|.
-- | The question of unification then becomes the question of finding coequalizers.
--   Bla {...} most general {...} uniqueness


-- [Definition]
-- | We say that a category /has unification/ if a proof of [..]
--   can be constructed.
record hasUnification (𝒞 : Category 𝑗) : 𝒰 𝑗 where
  -- |> For this we require there to be a function [...,]
  field unify : {a b : ⟨ 𝒞 ⟩} -> (f g : a ⟶ b) -> (¬ hasCoequalizerCandidate (f , g)) +-𝒰 (hasCoequalizer f g)
  -- |> which, for every parallel pair of arrows |f| and |g| decides whether
  --    a coequalizer exists, or that not even a coequalizer candidate exists.

open hasUnification {{...}} public
-- //




