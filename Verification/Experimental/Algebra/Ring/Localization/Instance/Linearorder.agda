
-- {-# OPTIONS --overlapping-instances #-}

module Verification.Experimental.Algebra.Ring.Localization.Instance.Linearorder where

open import Verification.Conventions

open import Verification.Experimental.Data.Prop.Everything
open import Verification.Experimental.Set.Setoid.Definition
open import Verification.Experimental.Algebra.Monoid.Definition
open import Verification.Experimental.Algebra.Group.Definition
-- open import Verification.Experimental.Algebra.Group.Quotient
open import Verification.Experimental.Algebra.Abelian.Definition
open import Verification.Experimental.Algebra.Ring.Definition
open import Verification.Experimental.Algebra.Ring.Localization
open import Verification.Experimental.Algebra.Ring.Ordered
open import Verification.Experimental.Algebra.Ring.Domain

open import Verification.Experimental.Order.Linearorder

record Repr {𝑖 𝑗 : 𝔏} {A : 𝒰 𝑖} {{_ : isSetoid 𝑗 A}} (P : A -> 𝒰 𝑘) (a : A) : 𝒰 (𝑖 ､ 𝑗 ､ 𝑘) where
  constructor mkrepr
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

  hasPositiveDenom : Localize R M -> 𝒰 _
  hasPositiveDenom (a / (da ∢ _)) = isPositive da

module _ {𝑖 : 𝔏 ^ 2} {𝑗 : 𝔏} {R : CRing 𝑖} {M : MCS R}
         {{_ : isOrderedRing 𝑗 ′ ⟨ R ⟩ ′}}
         {{_ : hasNotZero-MCS M}}
         {{δ : hasRepr (Localize R M) hasPositiveDenom}} where

  -- instance
  --   hasRepr:hasPositiveDenom:Localize : hasRepr (Localize R M) hasPositiveDenom
  --   hasRepr:hasPositiveDenom:Localize = {!!}

  private
    -- δ = hasRepr:hasPositiveDenom:Localize

    instance _ = isDomain:OrderedRing

    <-Loc-impl : (a b : Localize R M) -> 𝒰 _
    <-Loc-impl a' b' with δ .repr a' | δ .repr b'
    ... | mkrepr (a / da) _ _ | mkrepr (b / db) _ _ = a ⋅ ⟨ db ⟩ < b ⋅ ⟨ da ⟩
      -- let a = 
      --     b = 
      -- in loc↑ a ⋅ ⟨ loc↓ b ⟩ < loc↑ b ⋅ ⟨ loc↓ a ⟩


  -- record <-Loc-impl (a b : Localize R M) : 𝒰 𝑗 where
  --   field repr-l : Repr hasPositiveDenom a
  --         repr-r : Repr hasPositiveDenom b
  --         expand : ⦋ hasPositiveDenom ⦌
  --         by-< : 
  -- LELoc (a / da) (b / db) = a ⋅ ⟨ db ⟩ < b ⋅ ⟨ da ⟩

    _<-Loc_ : (a b : Localize R M) -> 𝒰 _
    _<-Loc_ = Base< <-Loc-impl

    lem-10 : ∀{a : Localize R M} -> ¬ a <-Loc a
    lem-10 {a'} (incl p) = {!!} -- irrefl-< p

    lem-20 : ∀{a b : Localize R M} -> a <-Loc b -> ¬ b <-Loc a
    lem-20 (incl p) (incl q) = {!!} -- asym-< p q

    lem-30 : ∀{a b : Localize R M} -> a <-Loc b -> (c : Localize R M)
              -> (a <-Loc c) +-𝒰 (c <-Loc b)
    lem-30 {a'} {b'} (incl p) c' = {!!}
      -- let (a / (da ∢ _)) = ⟨ δ .repr a' ⟩
      --     (b / (db ∢ _)) = ⟨ δ .repr b' ⟩
      --     (c / (dc ∢ _)) = ⟨ δ .repr c' ⟩
      --     P₀ : a ⋅ dc ⋅ db < b ⋅ dc ⋅ da
      --     P₀ = a ⋅ dc ⋅ db   ⟨ assoc-l-⋅ ∙ (refl ≀⋅≀ comm-⋅) ∙ assoc-r-⋅ ⟩-∼-<
      --           a ⋅ db ⋅ dc   ⟨ stronglyMonotone-l-⋅ p (δ .repr c' .hasProperty) ⟩-<-∼
      --           b ⋅ da ⋅ dc   ⟨ assoc-l-⋅ ∙ (refl ≀⋅≀ comm-⋅) ∙ assoc-r-⋅ ⟩-∼
      --           b ⋅ dc ⋅ da   ∎

      --     P₁ = case compare-< P₀ (c ⋅ da ⋅ db) of
      --           (λ (P₂ : a ⋅ dc ⋅ db < c ⋅ da ⋅ db) ->
      --                 left (incl (cancel-⋅-<-r P₂ (δ .repr b' .hasProperty))))

      --           (λ (P₂ : c ⋅ da ⋅ db < b ⋅ dc ⋅ da) ->
      --                 let P₃ : c ⋅ db ⋅ da < b ⋅ dc ⋅ da
      --                     P₃ = c ⋅ db ⋅ da  ⟨ assoc-l-⋅ ∙ (refl ≀⋅≀ comm-⋅) ∙ assoc-r-⋅ ⟩-∼-<
      --                           c ⋅ da ⋅ db  ⟨ P₂ ⟩-<-∼
      --                           b ⋅ dc ⋅ da  ∎

      --                     P₄ : c ⋅ db < b ⋅ dc
      --                     P₄ = cancel-⋅-<-r P₃ (δ .repr a' .hasProperty)
      --                 in right (incl P₄))
      -- in P₁

    lem-40 : ∀{a b : Localize R M} -> ¬ a <-Loc b -> ¬ b <-Loc a -> a ∼ b
    lem-40 {a'} {b'} p q = {!!}
      -- let (a / (da ∢ daP)) = ⟨ δ .repr a' ⟩
      --     (b / (db ∢ dbP)) = ⟨ δ .repr b' ⟩

      --     P₂ : a ⋅ db ∼ b ⋅ da
      --     P₂ = connected-< (λ x -> p (incl x)) (λ y -> q (incl y))

      --     P₃ : ⟨ δ .repr a' ⟩ ∼ ⟨ δ .repr b' ⟩
      --     P₃ = incl (⨡-MCS , P₂ ≀⋅≀ refl)

      -- in (δ .repr a' .represents) ∙ P₃ ∙ (δ .repr b' .represents ⁻¹)

    lem-50 : ∀{a₀ a₁ b₀ b₁ : Localize R M} -> a₀ ∼ a₁ -> b₀ ∼ b₁ -> a₀ <-Loc b₀ -> a₁ <-Loc b₁
    lem-50 {a₀'} {a₁'} {b₀'} {b₁'} pa pb (incl q) = {!!}
      -- let (a₀ / (da₀ ∢ da₀P)) = ⟨ δ .repr a₀' ⟩
      --     (a₁ / (da₁ ∢ da₁P)) = ⟨ δ .repr a₁' ⟩
      --     (b₀ / (db₀ ∢ db₀P)) = ⟨ δ .repr b₀' ⟩
      --     (b₁ / (db₁ ∢ db₁P)) = ⟨ δ .repr b₁' ⟩

      --     P₀ : ⟨ δ .repr a₀' ⟩ ∼ ⟨ δ .repr a₁' ⟩
      --     P₀ = δ .repr a₀' .represents ⁻¹ ∙ pa ∙ δ .repr a₁' .represents

      --     P₁ : ⟨ δ .repr b₀' ⟩ ∼ ⟨ δ .repr b₁' ⟩
      --     P₁ = δ .repr b₀' .represents ⁻¹ ∙ pb ∙ δ .repr b₁' .represents

      --     P₀' : a₀ ⋅ da₁ ∼ a₁ ⋅ da₀
      --     P₀' = cancel-⋅-r (⟨ P₀ ⟩ .snd) (isNotZero-MCS (Proof (⟨ P₀ ⟩ .fst)))

      --     P₁' : b₀ ⋅ db₁ ∼ b₁ ⋅ db₀
      --     P₁' = cancel-⋅-r (⟨ P₁ ⟩ .snd) (isNotZero-MCS (Proof (⟨ P₁ ⟩ .fst)))

      --     -- P₂ : a₀ ⋅ db₀ ⋅ da₁ < b₀ ⋅ da₀ ⋅ da₁
      --     -- P₂ = stronglyMonotone-l-⋅ q (δ .repr a₁' .hasProperty)

      --     P₂ : a₁ ⋅ db₀ ⋅ da₀ < b₀ ⋅ da₁ ⋅ da₀
      --     P₂ = a₁ ⋅ db₀ ⋅ da₀   ⟨ assoc-l-⋅ ∙ (refl ≀⋅≀ comm-⋅ ) ∙ assoc-r-⋅ ⟩-∼-<
      --           a₁ ⋅ da₀ ⋅ db₀   ⟨ P₀' ⁻¹ ≀⋅≀ refl ⟩-∼-<
      --           a₀ ⋅ da₁ ⋅ db₀   ⟨ assoc-l-⋅ ∙ (refl ≀⋅≀ comm-⋅ ) ∙ assoc-r-⋅ ⟩-∼-<
      --           a₀ ⋅ db₀ ⋅ da₁   ⟨ stronglyMonotone-l-⋅ q (δ .repr a₁' .hasProperty) ⟩-<-∼
      --           b₀ ⋅ da₀ ⋅ da₁   ⟨ assoc-l-⋅ ∙ (refl ≀⋅≀ comm-⋅ ) ∙ assoc-r-⋅ ⟩-∼
      --           b₀ ⋅ da₁ ⋅ da₀   ∎

      --     P₂' : a₁ ⋅ db₀ < b₀ ⋅ da₁
      --     P₂' = cancel-⋅-<-r P₂ (δ .repr a₀' .hasProperty)

      --     P₃ : a₁ ⋅ db₁ ⋅ db₀ < b₁ ⋅ da₁ ⋅ db₀
      --     P₃ = a₁ ⋅ db₁ ⋅ db₀    ⟨ assoc-l-⋅ ∙ (refl ≀⋅≀ comm-⋅ ) ∙ assoc-r-⋅ ⟩-∼-<
      --           a₁ ⋅ db₀ ⋅ db₁    ⟨ stronglyMonotone-l-⋅ P₂' (δ .repr b₁' .hasProperty) ⟩-<-∼
      --           b₀ ⋅ da₁ ⋅ db₁    ⟨ assoc-l-⋅ ∙ (refl ≀⋅≀ comm-⋅ ) ∙ assoc-r-⋅ ⟩-∼
      --           b₀ ⋅ db₁ ⋅ da₁    ⟨ P₁' ≀⋅≀ refl ⟩-∼
      --           b₁ ⋅ db₀ ⋅ da₁    ⟨ assoc-l-⋅ ∙ (refl ≀⋅≀ comm-⋅ ) ∙ assoc-r-⋅ ⟩-∼
      --           b₁ ⋅ da₁ ⋅ db₀    ∎

      --     P₃' : a₁ ⋅ db₁ < b₁ ⋅ da₁
      --     P₃' = cancel-⋅-<-r P₃ (δ .repr b₀' .hasProperty)

      -- in incl P₃'


  instance
    isLinearorder:Localize : isLinearorder _ ′ Localize R M ′
    isLinearorder.my< isLinearorder:Localize = <-Loc-impl
    isLinearorder.irrefl-< isLinearorder:Localize = lem-10
    isLinearorder.asym-< isLinearorder:Localize = lem-20
    isLinearorder.compare-< isLinearorder:Localize = lem-30
    isLinearorder.connected-< isLinearorder:Localize = lem-40
    isLinearorder.transp-< isLinearorder:Localize = lem-50



      -- lem-10 : ∀{a : Localize R M} -> a <-Loc a
      -- lem-10 {a'} = incl refl-<
        -- let (a / (da ∢ _)) = ⟨ δ .repr a' ⟩
        --     -- P : a ⋅ da < a ⋅ da
        --     -- P = refl-<
        -- in incl (refl-<)

{-
      lem-20 : ∀{a b c : Localize R M} -> a <-Loc b -> b <-Loc c -> a <-Loc c
      lem-20 {a'} {b'} {c'} (incl p) (incl q) =
        let (a / (da ∢ _)) = ⟨ δ .repr a' ⟩
            (b / (db ∢ _)) = ⟨ δ .repr b' ⟩
            (c / (dc ∢ _)) = ⟨ δ .repr c' ⟩

            P₀ : a ⋅ db ⋅ dc < b ⋅ da ⋅ dc
            P₀ = stronglyMonotone-l-⋅ p (δ .repr c' .hasProperty .π-<)

            P₁ : b ⋅ dc ⋅ da < c ⋅ db ⋅ da
            P₁ = stronglyMonotone-l-⋅ q (δ .repr a' .hasProperty .π-<)

            P₁ : a ⋅ dc ⋅ db < c ⋅ da ⋅ db
            P₁ = a ⋅ dc ⋅ db   ⟨ by-∼-< assoc-l-⋅ ∙ (refl ≀⋅≀ comm-⋅) ∙ assoc-r-⋅ ⟩-<
                 a ⋅ db ⋅ dc   ⟨ P₀ ⟩-<
                 b ⋅ da ⋅ dc   ⟨ by-∼-< assoc-l-⋅ ∙ (refl ≀⋅≀ comm-⋅) ∙ assoc-r-⋅ ⟩-<
                 b ⋅ dc ⋅ da   ⟨ P₁ ⟩-<
                 c ⋅ db ⋅ da   ⟨ by-∼-< assoc-l-⋅ ∙ (refl ≀⋅≀ comm-⋅) ∙ assoc-r-⋅ ⟩-<
                 c ⋅ da ⋅ db   ∎-<

        in {!!}

    instance
      isPreorder:Localize : isPreorder _ ′ Localize R M ′
      isPreorder.myLE isPreorder:Localize = <-Loc-impl
      isPreorder.refl-< isPreorder:Localize = lem-10
      isPreorder._∙-<_ isPreorder:Localize = lem-20
      isPreorder.transp-< isPreorder:Localize = {!!}

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
-}
