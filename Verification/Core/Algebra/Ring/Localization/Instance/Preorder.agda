
-- {-# OPTIONS --overlapping-instances #-}

module Verification.Core.Algebra.Ring.Localization.Instance.Preorder where

open import Verification.Conventions

open import Verification.Core.Algebra.Setoid.Definition
open import Verification.Core.Algebra.Monoid.Definition
open import Verification.Core.Algebra.Group.Definition
-- open import Verification.Core.Algebra.Group.Quotient
open import Verification.Core.Algebra.Abelian.Definition
open import Verification.Core.Algebra.Ring.Definition
open import Verification.Core.Algebra.Ring.Localization
open import Verification.Core.Algebra.Ring.Ordered
open import Verification.Core.Algebra.Ring.Domain

open import Verification.Core.Order.Preorder



record Repr {𝑖 𝑗 : 𝔏} {A : 𝒰 𝑖} {{_ : isSetoid 𝑗 A}} (P : A -> 𝒰 𝑘) (a : A) : 𝒰 (𝑖 ､ 𝑗 ､ 𝑘) where
  field ⟨_⟩ : A
  field represents : a ∼ ⟨_⟩
  field hasProperty : P ⟨_⟩
open Repr public

record hasRepr {𝑖 𝑗 : 𝔏} (A : 𝒰 𝑖) {{_ : isSetoid 𝑗 A}} (P : A -> 𝒰 𝑘) : 𝒰 (𝑖 ､ 𝑗 ､ 𝑘) where
  field repr : ∀(a : A) -> Repr P a
open hasRepr public

-- module _ {A : CRing (ℓ₀ , ℓ₀)} {M : MCS A} where
-- module _ {𝑖 : 𝔏 ^ 2} {R : CRing 𝑖} {M : MCS R} where
module _ {𝑖 : 𝔏 ^ 2} {𝑗 : 𝔏} {R : CRing 𝑖} {M : MCS R} {{_ : isOrderedRing 𝑗 ′ ⟨ R ⟩ ′}} where
  -- loc↑ = Localize.numer
  -- loc↓ = Localize.denom

  -- positive denominator
  hasPositiveDenom : Localize R M -> 𝒰 _
  hasPositiveDenom (a / (da ∈ _)) = isPositive da

module _ {𝑖 : 𝔏 ^ 2} {𝑗 : 𝔏} {R : CRing 𝑖} {M : MCS R} {{_ : isOrderedRing 𝑗 ′ ⟨ R ⟩ ′}} {{_ : isDomain ′ ⟨ R ⟩ ′}} where
  module _ {{δ : hasRepr (Localize R M) hasPositiveDenom}} where
    private
      ≤-Loc-impl : (a b : Localize R M) -> 𝒰 _
      ≤-Loc-impl a' b' =
        let a = ⟨ δ .repr a' ⟩
            b = ⟨ δ .repr b' ⟩
        in loc↑ a ⋅ ⟨ loc↓ b ⟩ ≤ loc↑ b ⋅ ⟨ loc↓ a ⟩

        -- let (a / (da ∈ _)) = ⟨ δ .repr a' ⟩
        --     (b / (db ∈ _)) = ⟨ δ .repr b' ⟩
        -- in ∑ λ (s : ⦋ isPositive ⦌) -> a ⋅ db ⋅ ⟨ s ⟩ ≤ b ⋅ da ⋅ ⟨ s ⟩

    -- record ≤-Loc-impl (a b : Localize R M) : 𝒰 𝑗 where
    --   field repr-l : Repr hasPositiveDenom a
    --         repr-r : Repr hasPositiveDenom b
    --         expand : ⦋ hasPositiveDenom ⦌
    --         by-≤ : 
    -- LELoc (a / da) (b / db) = a ⋅ ⟨ db ⟩ ≤ b ⋅ ⟨ da ⟩

      _≤-Loc_ : (a b : Localize R M) -> 𝒰 _
      _≤-Loc_ = LE ≤-Loc-impl

      lem-10 : ∀{a : Localize R M} -> a ≤-Loc a
      lem-10 {a'} = incl refl-≤
        -- let (a / (da ∈ _)) = ⟨ δ .repr a' ⟩
        --     -- P : a ⋅ da ≤ a ⋅ da
        --     -- P = refl-≤
        -- in incl (refl-≤)

      lem-20 : ∀{a b c : Localize R M} -> a ≤-Loc b -> b ≤-Loc c -> a ≤-Loc c
      lem-20 {a'} {b'} {c'} (incl p) (incl q) =
        let (a / (da ∈ _)) = ⟨ δ .repr a' ⟩
            (b / (db ∈ _)) = ⟨ δ .repr b' ⟩
            (c / (dc ∈ _)) = ⟨ δ .repr c' ⟩

            P₀ : a ⋅ db ⋅ dc ≤ b ⋅ da ⋅ dc
            P₀ = cong-⋅-≤-r p (δ .repr c' .hasProperty .π-≤)

            P₁ : b ⋅ dc ⋅ da ≤ c ⋅ db ⋅ da
            P₁ = cong-⋅-≤-r q (δ .repr a' .hasProperty .π-≤)

            P₁ : a ⋅ dc ⋅ db ≤ c ⋅ da ⋅ db
            P₁ = a ⋅ dc ⋅ db   ⟨ by-∼-≤ assoc-l-⋅ ∙ (refl ≀⋅≀ comm-⋅) ∙ assoc-r-⋅ ⟩-≤
                 a ⋅ db ⋅ dc   ⟨ P₀ ⟩-≤
                 b ⋅ da ⋅ dc   ⟨ by-∼-≤ assoc-l-⋅ ∙ (refl ≀⋅≀ comm-⋅) ∙ assoc-r-⋅ ⟩-≤
                 b ⋅ dc ⋅ da   ⟨ P₁ ⟩-≤
                 c ⋅ db ⋅ da   ⟨ by-∼-≤ assoc-l-⋅ ∙ (refl ≀⋅≀ comm-⋅) ∙ assoc-r-⋅ ⟩-≤
                 c ⋅ da ⋅ db   ∎-≤

        in {!!}

    instance
      isPreorder:Localize : isPreorder _ ′ Localize R M ′
      isPreorder.myLE isPreorder:Localize = ≤-Loc-impl
      isPreorder.refl-≤ isPreorder:Localize = lem-10
      isPreorder._∙-≤_ isPreorder:Localize = lem-20
      isPreorder.transp-≤ isPreorder:Localize = {!!}

{-
{-

-}



-- record _:&2_ (UU : 𝒰 𝑖) {{U : hasU UU 𝑘 𝑙}} {Q : UU -> 𝒰 𝑗₁} (P : (u : UU) -> Q u -> 𝒰 𝑗) : 𝒰 (𝑗 ､ 𝑘 ､ 𝑙 ､ 𝑗₁) where
--   constructor ′_′
--   field ⟨_⟩ : getU U
--   -- field overlap {{oldProof}} : getP U ⟨_⟩
--   field {oldProof} : getP U ⟨_⟩
--   field overlap {{ProofQ}} : Q (reconstruct U (⟨_⟩ , oldProof))
--   field overlap {{Proof}} : P (reconstruct U (⟨_⟩ , oldProof)) ProofQ
-- open _:&2_ {{...}} public hiding (⟨_⟩)
-- open _:&2_ public using (⟨_⟩)

-- infixl 30 _:&2_

-}
