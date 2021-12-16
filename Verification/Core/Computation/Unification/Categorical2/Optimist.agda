
module Verification.Core.Computation.Unification.Categorical2.Optimist where

open import Verification.Conventions
open import Verification.Core.Set.Setoid
open import Verification.Core.Order.Preorder
open import Verification.Core.Order.Lattice
open import Verification.Core.Order.WellFounded.Definition
open import Verification.Core.Data.Universe.Definition
open import Verification.Core.Data.Universe.Instance.Category
open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Category.Std.Category.Sized.Definition
open import Verification.Core.Category.Std.Morphism.Epi.Definition
open import Verification.Core.Category.Std.Category.As.ZeroMorphismCategory.Definition
open import Verification.Core.Computation.Unification.Categorical2.Ideal
open import Verification.Core.Computation.Unification.Categorical2.ForwardAction
open import Verification.Core.Computation.Unification.Categorical2.SemilatticeStructure
open import Verification.Core.Computation.Unification.Categorical2.ZeroIdeal
open import Verification.Core.Computation.Unification.Categorical2.EpiPrincipal
open import Verification.Core.Computation.Unification.Categorical2.InverseAction


-- ===* Statement and proof of the lemma
-- | With this, the optimist's lemma can finally be stated and proved


-- [Hide]
module _ (𝒞 : 𝒰 𝑖)
  {{_ : isCategory {𝑗} 𝒞 }}
  {{_ : isSizedCategory ′ 𝒞 ′}}
  {{_ : isZeroMorphismCategory ′ 𝒞 ′}} where

  private variable a : 𝒞

-- //

-- [Lemma]
-- | Let [..] be two ideals at |a|.
  module _ {U V : Ideal a} where
    -- |> Assume that we have a proof [..].
    module _ (PU : isEpiPrincipal U) where
      private instance _ = PU
      -- |> Let the representing morphism of |U| be called |u|:
      u : a ⟶ repObjOf U
      u = repOf U

      -- |> and assume that we also have a proof [....]
      module _ (PV : isEpiPrincipal (u ⁻¹↷ V)) where

      -- |> Then |isEpiPrincipal (V ∧ U)| is true.

-- //

-- [Proof]
        private instance _ = PV

        -- | Denote the representing morphism of |u ⁻¹↷ V| by |v|.
        v : repObjOf U ⟶ repObjOf (u ⁻¹↷ V)
        v = repOf (u ⁻¹↷ V)

        -- |> Then the following chain of equations holds:
        lem-1 : (V ∧ U) ∼ (u ◆ v) ↷ ⊤
        lem-1 =  V ∧ U                      ⟨ refl ≀∧≀ principal-r ⟩-∼
                  (V ∧ (u ↷ ⊤))              ⟨ inv-↷-r ⁻¹ ⟩-∼
                  (u ↷ (u ⁻¹↷ V))            ⟨ refl ≀↷≀ (principal-r)  ⟩-∼
                  (u ↷ (v ↷ ⊤))              ⟨ assoc-l-↷ ⁻¹ ⟩-∼
                  ((u ◆ v) ↷ ⊤)              ∎

        -- |> Using |u ◆ v| as representing morphism, we conclude.
        Proof : isEpiPrincipal (V ∧ U)
        Proof = record
                  { repObj       = _
                  ; rep          = u ◆ v
                  ; principal-r  = lem-1
                  ; zeroOrEpi    = isZeroOrEpi:◆ {𝒞' = ′ 𝒞 ′} zeroOrEpi zeroOrEpi
                  ; isGoodRep    = isGood:◆ isGoodRep isGoodRep
                  }

        -- |> We also need to use the fact that the property |isZeroOrEpi|
        --    is preserved by composition. Furthermore, the field |isGoodRep|
        --    needs to be set. This is part of the infrastructure for the induction.

-- //

{-
    module _  (PV : isEpiPrincipal (repOf U {{PU}} ⁻¹↷ V)) where

    optimist : 
              -> isEpiPrincipal (V ∧ U)
    optimist {a} {U} {V} PU PV =
      let
          instance _ = PV


          V' = u ⁻¹↷ V

          v : repObjOf U ⟶ repObjOf V'
          v = repOf V'

          P₈ : (V ∧ U) ∼ (u ◆ v) ↷ ⊤
          P₈ = V ∧ U                                          ⟨ refl ≀∧≀ principal-r ⟩-∼
                (V ∧ (u ↷ ⊤))                                 ⟨ inv-↷-r ⁻¹ ⟩-∼
                (u ↷ ((u ⁻¹↷ V)))                              ⟨ refl ≀↷≀ (principal-r)  ⟩-∼
                (u ↷ ((v ↷ ⊤)))                                ⟨ assoc-l-↷ ⁻¹ ⟩-∼
                ((u ◆ v) ↷ ⊤)                                   ∎

      in record
         { repObj = _
         ; rep = u ◆ v
         ; principal-r = P₈
         ; isGoodRep = isGood:◆ isGoodRep isGoodRep
         ; zeroOrEpi = isZeroOrEpi:◆ {𝒞' = ′ 𝒞 ′} zeroOrEpi zeroOrEpi
         }
-}

