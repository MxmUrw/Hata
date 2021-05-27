
-- {-# OPTIONS --overlapping-instances #-}

module Verification.Experimental.Algebra.Ring.Localization.Instance.Monoid where

open import Verification.Conventions
open import Verification.Experimental.Meta.Structure
open import Verification.Experimental.Set.Setoid.Definition
open import Verification.Experimental.Algebra.Monoid.Definition
open import Verification.Experimental.Algebra.Group.Definition
-- open import Verification.Experimental.Algebra.Group.Quotient
open import Verification.Experimental.Algebra.Abelian.Definition
open import Verification.Experimental.Algebra.Ring.Definition
open import Verification.Experimental.Algebra.Ring.Localization.Definition
open import Verification.Experimental.Algebra.Ring.Localization.Instance.Setoid

─ = refl

module _ {𝑖 : 𝔏 ^ 2} {R : CRing 𝑖} {M : MCS R} where
  -- mytest2 : isRing ′ ⟨ R ⟩ ′
  -- mytest2 = it

  -- mytest3 : isSetoid _ (Localize R M)
  -- mytest3 = it

  -- myrefltest : ∀{a : Localize R M} -> a ∼ a
  -- myrefltest = refl {{isSetoid:Localize}}

  private
    _⋆-Loc_ : Localize R M -> Localize R M -> Localize R M
    _⋆-Loc_ (a / da) (b / db) = (a ⋅ ⟨ db ⟩ ⋆ b ⋅ ⟨ da ⟩) / (da ⋅-MCS db)
    infixl 50 _⋆-Loc_

    ◌-Loc : Localize R M
    ◌-Loc = ◌ / ⨡-MCS

    -- | ⋆ on Localize is commutative:
    lem-10 : ∀{a b : Localize R M} -> a ⋆-Loc b ∼ b ⋆-Loc a
    lem-10 {a / (da ∈ _)} {b / (db ∈ _)} =
      let P : (a ⋅ db ⋆ b ⋅ da) ⋅ (db ⋅ da) ⋅ ⨡  ∼  (b ⋅ da ⋆ a ⋅ db) ⋅ (da ⋅ db) ⋅ ⨡
          P = (a ⋅ db ⋆ b ⋅ da) ⋅ (db ⋅ da) ⋅ ⨡  ≣⟨ comm-⋆ ≀⋅≀ comm-⋅ ≀⋅≀ ─ ⟩
              (b ⋅ da ⋆ a ⋅ db) ⋅ (da ⋅ db) ⋅ ⨡  ∎
      in incl (⨡-MCS , P)

    -- | ◌ is left unit
    lem-20 : ∀{a : Localize R M} -> ◌-Loc ⋆-Loc a ∼ a
    lem-20 {a / (da ∈ _)} =
      let P₅ : ((◌ ⋅ da) ⋆ (a ⋅ ⨡)) ⋅ da ⋅ ⨡  ∼  a ⋅ (⨡ ⋅ da) ⋅ ⨡
          P₅ = ((◌ ⋅ da) ⋆ (a ⋅ ⨡)) ⋅ da ⋅ ⨡   ≣⟨ (reduce-⋅◌-l ≀⋆≀ ─) ≀⋅≀ ─ ≀⋅≀ ─ ⟩
               (◌ ⋆ (a ⋅ ⨡)) ⋅ da ⋅ ⨡          ≣⟨ unit-l-⋆ ≀⋅≀ ─ ≀⋅≀ ─ ⟩
               (a ⋅ ⨡) ⋅ da ⋅ ⨡                ≣⟨ assoc-l-⋅ ≀⋅≀ ─ ⟩
               a ⋅ (⨡ ⋅ da) ⋅ ⨡                ∎
      in incl (⨡-MCS , P₅)

    -- | ◌ is right unit
    lem-30 : ∀{a : Localize R M} -> a ⋆-Loc ◌-Loc ∼ a
    lem-30 {a} = lem-10 ∙ lem-20

    -- | ⋆ is associative
    lem-40 : ∀{a b c : Localize R M} -> (a ⋆-Loc b) ⋆-Loc c ∼ a ⋆-Loc (b ⋆-Loc c)
    lem-40 {a / (da ∈ _)} {b / (db ∈ _)} {c / (dc ∈ _)} =
      let P₀ : ((a ⋅ db ⋆ b ⋅ da) ⋅ dc ⋆ c ⋅ (da ⋅ db))  ∼  (a ⋅ (db ⋅ dc) ⋆ (b ⋅ dc ⋆ c ⋅ db) ⋅ da)
          P₀ = (a ⋅ db ⋆ b ⋅ da) ⋅ dc ⋆ c ⋅ (da ⋅ db)         ≣⟨ distr-r-⋅ ≀⋆≀ ─ ⟩
               a ⋅ db ⋅ dc ⋆ b ⋅ da ⋅ dc ⋆ c ⋅ (da ⋅ db)      ≣⟨ assoc-l-⋅ ≀⋆≀ (assoc-l-⋅ ∙ (─ ≀⋅≀ comm-⋅) ∙ assoc-r-⋅) ≀⋆≀ ((─ ≀⋅≀ comm-⋅) ∙ assoc-r-⋅) ⟩
               a ⋅ (db ⋅ dc) ⋆ (b ⋅ dc) ⋅ da ⋆ (c ⋅ db) ⋅ da  ≣⟨ assoc-l-⋆ ⟩
              a ⋅ (db ⋅ dc) ⋆ ((b ⋅ dc) ⋅ da ⋆ (c ⋅ db) ⋅ da) ≣⟨ ─ ≀⋆≀ distr-r-⋅ ⁻¹ ⟩
              (a ⋅ (db ⋅ dc) ⋆ (b ⋅ dc ⋆ c ⋅ db) ⋅ da)        ∎

          P₁ : ((a ⋅ db ⋆ b ⋅ da) ⋅ dc ⋆ c ⋅ (da ⋅ db)) ⋅ (da ⋅ (db ⋅ dc)) ⋅ ⨡  ∼  (a ⋅ (db ⋅ dc) ⋆ (b ⋅ dc ⋆ c ⋅ db) ⋅ da) ⋅ (da ⋅ db ⋅ dc) ⋅ ⨡
          P₁ = P₀ ≀⋅≀ assoc-r-⋅ ≀⋅≀ ─
      in incl (⨡-MCS , P₁)

    -- | ∼ is congruence over ⋆
    lem-50 : ∀{a₀ a₁ b₀ b₁ : Localize R M} -> a₀ ∼ a₁ -> b₀ ∼ b₁ -> a₀ ⋆-Loc b₀ ∼ a₁ ⋆-Loc b₁
    lem-50 {a₀ / (da₀ ∈ Da₀)} {a₁ / (da₁ ∈ Da₁)} {b₀ / (db₀ ∈ Db₀)} {b₁ / (db₁ ∈ Db₁)} (incl (t , p)) (incl (s , q)) =
      let dt = ⟨ t ⟩
          ds = ⟨ s ⟩


          P₀ : ∀{a₀ a₁ da₀ da₁ db₀ db₁ dt ds  : ⟨ R ⟩}
               -> (p : a₀ ⋅ da₁ ⋅ dt ∼ a₁ ⋅ da₀ ⋅ dt)
               -> (a₀ ⋅ db₀) ⋅ ((da₁ ⋅ db₁) ⋅ (dt ⋅ ds))  ∼  (a₁ ⋅ db₁) ⋅ ((da₀ ⋅ db₀) ⋅ (dt ⋅ ds))
          P₀ {a₀} {a₁} {da₀} {da₁} {db₀} {db₁} {dt} {ds} p =
               (a₀ ⋅ db₀) ⋅ ((da₁ ⋅ db₁) ⋅ (dt ⋅ ds))    ≣⟨ ─ ≀⋅≀ assoc-r-⋅ ⟩
               (a₀ ⋅ db₀) ⋅ ((da₁ ⋅ db₁) ⋅ dt ⋅ ds)      ≣⟨ ─ ≀⋅≀ (assoc-l-⋅ ≀⋅≀ ─) ⟩
               (a₀ ⋅ db₀) ⋅ (da₁ ⋅ (db₁ ⋅ dt) ⋅ ds)      ≣⟨ ─ ≀⋅≀ (─ ≀⋅≀ comm-⋅ ≀⋅≀ ─) ⟩
               (a₀ ⋅ db₀) ⋅ (da₁ ⋅ (dt ⋅ db₁) ⋅ ds)      ≣⟨ ─ ≀⋅≀ (assoc-r-⋅ ≀⋅≀ ─) ⟩
               (a₀ ⋅ db₀) ⋅ ((da₁ ⋅ dt) ⋅ db₁ ⋅ ds)      ≣⟨ assoc-l-⋅ ⟩
               a₀ ⋅ (db₀ ⋅ ((da₁ ⋅ dt) ⋅ db₁ ⋅ ds))      ≣⟨ ─ ≀⋅≀ assoc-r-⋅ ⟩
               a₀ ⋅ (db₀ ⋅ ((da₁ ⋅ dt) ⋅ db₁) ⋅ ds)      ≣⟨ ─ ≀⋅≀ (comm-⋅ ≀⋅≀ ─) ⟩
               a₀ ⋅ (((da₁ ⋅ dt) ⋅ db₁) ⋅ db₀ ⋅ ds)      ≣⟨ assoc-r-⋅ ⟩
               (a₀ ⋅ (((da₁ ⋅ dt) ⋅ db₁) ⋅ db₀)) ⋅ ds    ≣⟨ assoc-r-⋅ ≀⋅≀ ─ ⟩
               (a₀ ⋅ ((da₁ ⋅ dt) ⋅ db₁) ⋅ db₀) ⋅ ds      ≣⟨ assoc-r-⋅ ≀⋅≀ ─ ≀⋅≀ ─ ⟩
               (a₀ ⋅ (da₁ ⋅ dt) ⋅ db₁ ⋅ db₀) ⋅ ds        ≣⟨ assoc-r-⋅ ≀⋅≀ ─ ≀⋅≀ ─ ≀⋅≀ ─ ⟩
               (a₀ ⋅ da₁ ⋅ dt ⋅ db₁ ⋅ db₀) ⋅ ds          ≣⟨ p ≀⋅≀ ─ ≀⋅≀ ─ ≀⋅≀ ─ ⟩
               (a₁ ⋅ da₀ ⋅ dt ⋅ db₁ ⋅ db₀) ⋅ ds          ≣⟨ assoc-l-⋅ ≀⋅≀ ─ ≀⋅≀ ─ ≀⋅≀ ─ ⟩
               (a₁ ⋅ (da₀ ⋅ dt) ⋅ db₁ ⋅ db₀) ⋅ ds        ≣⟨ assoc-l-⋅ ≀⋅≀ ─ ≀⋅≀ ─ ⟩
               (a₁ ⋅ ((da₀ ⋅ dt) ⋅ db₁) ⋅ db₀) ⋅ ds      ≣⟨ ─ ≀⋅≀ comm-⋅ ≀⋅≀ ─ ≀⋅≀ ─ ⟩
               (a₁ ⋅ (db₁ ⋅ (da₀ ⋅ dt)) ⋅ db₀) ⋅ ds      ≣⟨ assoc-r-⋅ ≀⋅≀ ─ ≀⋅≀ ─ ⟩
               (a₁ ⋅ db₁) ⋅ (da₀ ⋅ dt) ⋅ db₀ ⋅ ds        ≣⟨ assoc-l-⋅ ≀⋅≀ ─ ⟩
               (a₁ ⋅ db₁) ⋅ ((da₀ ⋅ dt) ⋅ db₀) ⋅ ds      ≣⟨ ─ ≀⋅≀ (assoc-l-⋅ ∙ (─ ≀⋅≀ comm-⋅) ∙ assoc-r-⋅) ≀⋅≀ ─ ⟩
               (a₁ ⋅ db₁) ⋅ ((da₀ ⋅ db₀) ⋅ dt) ⋅ ds      ≣⟨ assoc-l-⋅ ⟩
               (a₁ ⋅ db₁) ⋅ (((da₀ ⋅ db₀) ⋅ dt) ⋅ ds)    ≣⟨ ─ ≀⋅≀ assoc-l-⋅ ⟩
               (a₁ ⋅ db₁) ⋅ ((da₀ ⋅ db₀) ⋅ (dt ⋅ ds))    ∎

          -- | We switch a₀, a₁ and their ds using p
          P₁ : (a₀ ⋅ db₀) ⋅ ((da₁ ⋅ db₁) ⋅ (dt ⋅ ds))  ∼  (a₁ ⋅ db₁) ⋅ ((da₀ ⋅ db₀) ⋅ (dt ⋅ ds))
          P₁ = P₀ p

          -- | We switch b₀, b₁ and their ds using q
          P₂ : (b₀ ⋅ da₀) ⋅ ((da₁ ⋅ db₁) ⋅ (dt ⋅ ds))  ∼  (b₁ ⋅ da₁) ⋅ ((da₀ ⋅ db₀) ⋅ (dt ⋅ ds))
          P₂ = (b₀ ⋅ da₀) ⋅ ((da₁ ⋅ db₁) ⋅ (dt ⋅ ds))    ≣⟨ ─ ≀⋅≀ (comm-⋅ ≀⋅≀ comm-⋅) ⟩
               (b₀ ⋅ da₀) ⋅ ((db₁ ⋅ da₁) ⋅ (ds ⋅ dt))    ≣⟨ P₀ q ⟩
               (b₁ ⋅ da₁) ⋅ ((db₀ ⋅ da₀) ⋅ (ds ⋅ dt))    ≣⟨ ─ ≀⋅≀ (comm-⋅ ≀⋅≀ comm-⋅) ⟩
               (b₁ ⋅ da₁) ⋅ ((da₀ ⋅ db₀) ⋅ (dt ⋅ ds))    ∎

          -- | We put both proofs together
          P₃ : (a₀ ⋅ db₀ ⋆ b₀ ⋅ da₀) ⋅ (da₁ ⋅ db₁) ⋅ (dt ⋅ ds)  ∼  (a₁ ⋅ db₁ ⋆ b₁ ⋅ da₁) ⋅ (da₀ ⋅ db₀) ⋅ (dt ⋅ ds)
          P₃ = (a₀ ⋅ db₀ ⋆ b₀ ⋅ da₀) ⋅ (da₁ ⋅ db₁) ⋅ (dt ⋅ ds)     ≣⟨ assoc-l-⋅ ⟩
               (a₀ ⋅ db₀ ⋆ b₀ ⋅ da₀) ⋅ ((da₁ ⋅ db₁) ⋅ (dt ⋅ ds))   ≣⟨ distr-r-⋅ ⟩
               (a₀ ⋅ db₀) ⋅ ((da₁ ⋅ db₁) ⋅ (dt ⋅ ds))   ⋆   (b₀ ⋅ da₀) ⋅ ((da₁ ⋅ db₁) ⋅ (dt ⋅ ds))   ≣⟨ P₁ ≀⋆≀ P₂ ⟩

               (a₁ ⋅ db₁) ⋅ ((da₀ ⋅ db₀) ⋅ (dt ⋅ ds))   ⋆   (b₁ ⋅ da₁) ⋅ ((da₀ ⋅ db₀) ⋅ (dt ⋅ ds))    ≣⟨ distr-r-⋅ ⁻¹ ⟩
               (a₁ ⋅ db₁ ⋆ b₁ ⋅ da₁) ⋅ ((da₀ ⋅ db₀) ⋅ (dt ⋅ ds))   ≣⟨ assoc-r-⋅ ⟩
               (a₁ ⋅ db₁ ⋆ b₁ ⋅ da₁) ⋅ (da₀ ⋅ db₀) ⋅ (dt ⋅ ds) ∎

      in incl (t ⋅-MCS s , P₃)


  instance
    isMonoid:Localize : isMonoid ′ Localize R M ′
    isMonoid._⋆_ isMonoid:Localize = _⋆-Loc_
    isMonoid.◌ isMonoid:Localize = ◌-Loc
    isMonoid.unit-l-⋆ isMonoid:Localize = lem-20
    isMonoid.unit-r-⋆ isMonoid:Localize = lem-30
    isMonoid.assoc-l-⋆ isMonoid:Localize = lem-40
    isMonoid.assoc-r-⋆ isMonoid:Localize = lem-40 ⁻¹
    isMonoid._`cong-⋆`_ isMonoid:Localize = lem-50


  instance
    isCommutative:Localize : isCommutative ′ Localize R M ′
    isCommutative.comm-⋆ isCommutative:Localize = lem-10







