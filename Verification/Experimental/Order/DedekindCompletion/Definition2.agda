
module Verification.Core.Order.DedekindCompletion.Definition2 where

open import Verification.Conventions
open import Verification.Core.Data.Int.Definition
open import Verification.Core.Data.Rational.Definition

open import Verification.Core.Algebra.Setoid
open import Verification.Core.Order.Linearorder

-- mostly from https://ncatlab.org/nlab/show/real+number
-- and https://ncatlab.org/nlab/show/Dedekind+cut



module _ {𝑖 : 𝔏 ^ 3} (X : Linearorder 𝑖) where

  record isCut {LI LU : 𝒰 𝑗} (L : LI -> ⟨ X ⟩) (U : LU -> ⟨ X ⟩) : 𝒰 (𝑗 ､ 𝑖) where
    field inhabited-⩘ : LI
    field open-⩘ : ∀{a : LI} -> ∑ λ (b : LI) -> L a < L b
    field compare-Cut : ∀{a b : ⟨ X ⟩} -> a < b -> (∑ λ i -> L i ∼ a) +-𝒰 (∑ λ i -> U i ∼ b)

  record Cut (𝑗 : 𝔏) : 𝒰 (𝑗 ⁺ ､ 𝑖) where
    -- constructor _,_
    constructor cut
    field ⩘ : 𝒰 𝑗
          ⩘F : ⩘ -> ⟨ X ⟩
    field ⩗ : 𝒰 𝑗
          ⩗F : ⩗ -> ⟨ X ⟩
    field {{isCutProof}} : isCut ⩘F ⩗F

  open Cut public


module _ {𝑖 : 𝔏 ^ 3} {𝑗 : 𝔏} {X : Linearorder 𝑖} where

  instance
    isSetoid:Cut : isSetoid _ (Cut X 𝑗)
    isSetoid.myRel isSetoid:Cut (cut C1 C1F C2 C2F) (cut D1 D1F D2 D2F) = ∀(i : C1) -> ∑ λ (j : D1) -> C1F i ∼ D1F j
    isSetoid.isEquivRel:∼ isSetoid:Cut = {!!}

    isLinearorder:Cut : isLinearorder _ ′ Cut X 𝑗 ′
    isLinearorder.my< isLinearorder:Cut (cut C1 C1F C2 C2F) (cut D1 D1F D2 D2F) = ∑ λ (i : C1) -> ∑ λ (j : D2) -> C1F i ∼ D2F j
    isLinearorder.irrefl-< isLinearorder:Cut = {!!}
    isLinearorder.asym-< isLinearorder:Cut = {!!}
    isLinearorder.compare-< isLinearorder:Cut = {!!}
    isLinearorder.connected-< isLinearorder:Cut = {!!}
    isLinearorder.transp-< isLinearorder:Cut = {!!}

module _ {𝑖 : 𝔏 ^ 3} {X : Linearorder 𝑖} where
  embed-Cut : ⟨ X ⟩ -> Cut X (⨆ 𝑖) -- (𝑖 ⌄ 0 ⊔ 𝑖 ⌄ 2)
  Cut.⩘ (embed-Cut x) = Lift {j = ⨆ 𝑖} (∑ λ y -> y < x)
  Cut.⩘F (embed-Cut x) = {!!}
  Cut.⩗ (embed-Cut x) = {!!}
  Cut.⩗F (embed-Cut x) = {!!}
  Cut.isCutProof (embed-Cut x) = {!!}

module _ {𝑖 : 𝔏 ^ 3} {X : Linearorder 𝑖} where
  -- sup-Cut : {A : 𝒰 _} (F : A -> ⟨ X ⟩) -> \

  join-Cut : Cut ′ Cut X (⨆ 𝑖) ′ (⨆ 𝑖) -> Cut X (⨆ 𝑖)
  Cut.⩘ (join-Cut (cut L LF U UF)) =
    let X = ∑ λ (i : L) -> LF i .⩗
    in X
  Cut.⩘F (join-Cut (cut L LF U UF)) (i , ij) = LF i .⩗F ij
  Cut.⩗ (join-Cut (cut ⩘ ⩘F ⩗ ⩗F)) = {!!}
  Cut.⩗F (join-Cut (cut ⩘ ⩘F ⩗ ⩗F)) = {!!}
  Cut.isCutProof (join-Cut (cut ⩘ ⩘F ⩗ ⩗F)) = {!!}

{-
    constructor iscut
    field inhabited-⩘ : ⦋ ⟨ L ⟩ ⦌
    field inhabited-⩗ : ⦋ ⟨ U ⟩ ⦌
    field open-⩘ : ∀{a : ⟨ X ⟩} -> ⟨ L ⟩ a -> ∑ λ (b : ⦋ ⟨ L ⟩ ⦌) -> a < ⟨ b ⟩
    field open-⩗ : ∀{b : ⟨ X ⟩} -> ⟨ U ⟩ b -> ∑ λ (a : ⦋ ⟨ U ⟩ ⦌) -> ⟨ a ⟩ < b
    field compare-Cut : ∀{a b : ⟨ X ⟩} -> a < b -> ⟨ L ⟩ a +-𝒰 ⟨ U ⟩ b
    field by-⩘⩗-< : ∀{a b : ⟨ X ⟩} -> ⟨ L ⟩ a -> ⟨ U ⟩ b -> a < b

  open isCut {{...}} public

  record Cut : 𝒰 (((𝑖 .fst) ⁺) ⊔ 𝑖 ⌄ 1 ⊔ 𝑖 ⌄ 2) where
    constructor _,_
    field ⩘ : Subsetoid ′ ⟨ X ⟩ ′
    field ⩗ : Subsetoid ′ ⟨ X ⟩ ′
    field {{isCutProof}} : isCut ⩘ ⩗

  open Cut public
  -}
