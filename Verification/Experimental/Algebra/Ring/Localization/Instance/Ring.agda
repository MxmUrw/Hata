
module Verification.Experimental.Algebra.Ring.Localization.Instance.Ring where

open import Verification.Conventions

open import Verification.Experimental.Data.Prop.Everything
open import Verification.Experimental.Set.Setoid.Definition
open import Verification.Experimental.Algebra.Monoid.Definition
open import Verification.Experimental.Algebra.Group.Definition
-- open import Verification.Experimental.Algebra.Group.Quotient
open import Verification.Experimental.Algebra.Abelian.Definition
open import Verification.Experimental.Algebra.Ring.Definition
open import Verification.Experimental.Algebra.Ring.Localization.Definition
open import Verification.Experimental.Algebra.Ring.Localization.Instance.Setoid
open import Verification.Experimental.Algebra.Ring.Localization.Instance.Monoid
open import Verification.Experimental.Algebra.Ring.Localization.Instance.Group




module _ {𝑖 : 𝔏 ×-𝒰 𝔏} {R : CRing 𝑖} {M : MCS R} where
  private
    _⋅-Loc_ : (a b : Localize R M) -> Localize R M
    _⋅-Loc_ (a / da) (b / db) = (a ⋅ b) / (da ⋅-MCS db)
    infixl 80 _⋅-Loc_

    ⨡-Loc : Localize R M
    ⨡-Loc = ⨡ / ⨡-MCS

    lem-10 : ∀{a b : Localize R M} -> a ⋅-Loc b ∼ b ⋅-Loc a
    lem-10 {a / (da ∢ _)} {b / (db ∢ _)} =
      let P : (a ⋅ b) ⋅ (db ⋅ da) ∼ (b ⋅ a) ⋅ (da ⋅ db)
          P = comm-⋅ ≀⋅≀ comm-⋅
      in incl (⨡-MCS , P ≀⋅≀ ─)

    lem-20 : ∀{a : Localize R M} -> ⨡-Loc ⋅-Loc a ∼ a
    lem-20 {a / (da ∢ _)} =
      let P : (⨡ ⋅ a) ⋅ da ∼ a ⋅ (⨡ ⋅ da)
          P = (⨡ ⋅ a) ⋅ da   ≣⟨ unit-l-⋅ ≀⋅≀ ─ ⟩
              a ⋅ da         ≣⟨ ─ ≀⋅≀ unit-l-⋅ ⁻¹ ⟩
              a ⋅ (⨡ ⋅ da)   ∎

      in incl (⨡-MCS , P ≀⋅≀ ─)

    lem-30 : ∀{a b c : Localize R M} -> (a ⋅-Loc b) ⋅-Loc c ∼ a ⋅-Loc (b ⋅-Loc c)
    lem-30 {a / (da ∢ _)} {b / (db ∢ _)} {c / (dc ∢ _)} =
      let P : (a ⋅ b ⋅ c) ⋅ (da ⋅ (db ⋅ dc)) ∼ (a ⋅ (b ⋅ c)) ⋅ (da ⋅ db ⋅ dc)
          P = assoc-l-⋅ ≀⋅≀ assoc-r-⋅
      in incl (⨡-MCS , P ≀⋅≀ ─)

    lem-40 : ∀{a b c : Localize R M} -> a ⋅-Loc (b ⋆ c) ∼ (a ⋅-Loc b) ⋆ (a ⋅-Loc c)
    lem-40 {a / (da ∢ _)} {b / (db ∢ _)} {c / (dc ∢ _)} =
      let P₀ : ∀{a b da db dc : ⟨ R ⟩} -> (a ⋅ (b ⋅ dc)) ⋅ ((da ⋅ db) ⋅ (da ⋅ dc))  ∼  ((a ⋅ b) ⋅ (da ⋅ dc)) ⋅ (da ⋅ (db ⋅ dc))
          P₀ {a} {b} {da} {db} {dc} =
               (a ⋅ (b ⋅ dc)) ⋅ ((da ⋅ db) ⋅ (da ⋅ dc))  ≣⟨ assoc-r-⋅ ≀⋅≀ assoc-r-⋅ ⟩
               ((a ⋅ b) ⋅ dc) ⋅ (((da ⋅ db) ⋅ da) ⋅ dc)  ≣⟨ ─ ≀⋅≀ (assoc-l-⋅ ≀⋅≀ ─) ⟩
               ((a ⋅ b) ⋅ dc) ⋅ ((da ⋅ (db ⋅ da)) ⋅ dc)  ≣⟨ ─ ≀⋅≀ ((─ ≀⋅≀ comm-⋅) ≀⋅≀ ─) ⟩
               ((a ⋅ b) ⋅ dc) ⋅ ((da ⋅ (da ⋅ db)) ⋅ dc)  ≣⟨ ─ ≀⋅≀ assoc-l-⋅ ⟩
               ((a ⋅ b) ⋅ dc) ⋅ (da ⋅ ((da ⋅ db) ⋅ dc))  ≣⟨ ─ ≀⋅≀ (─ ≀⋅≀ assoc-l-⋅) ⟩
               ((a ⋅ b) ⋅ dc) ⋅ (da ⋅ (da ⋅ (db ⋅ dc)))  ≣⟨ assoc-l-⋅ ⟩
               (a ⋅ b) ⋅ (dc ⋅ (da ⋅ (da ⋅ (db ⋅ dc))))  ≣⟨ ─ ≀⋅≀ assoc-r-⋅ ⟩
               (a ⋅ b) ⋅ ((dc ⋅ da) ⋅ (da ⋅ (db ⋅ dc)))  ≣⟨ assoc-r-⋅ ⟩
               ((a ⋅ b) ⋅ (dc ⋅ da)) ⋅ (da ⋅ (db ⋅ dc))  ≣⟨ ─ ≀⋅≀ comm-⋅ ≀⋅≀ ─ ⟩
               ((a ⋅ b) ⋅ (da ⋅ dc)) ⋅ (da ⋅ (db ⋅ dc))  ∎

          P₁ : (a ⋅ (c ⋅ db)) ⋅ ((da ⋅ db) ⋅ (da ⋅ dc))  ∼  ((a ⋅ c) ⋅ (da ⋅ db)) ⋅ (da ⋅ (db ⋅ dc))
          P₁ = (a ⋅ (c ⋅ db)) ⋅ ((da ⋅ db) ⋅ (da ⋅ dc)) ≣⟨ ─ ≀⋅≀ comm-⋅ ⟩
               (a ⋅ (c ⋅ db)) ⋅ ((da ⋅ dc) ⋅ (da ⋅ db)) ≣⟨ P₀ ⟩
               ((a ⋅ c) ⋅ (da ⋅ db)) ⋅ (da ⋅ (dc ⋅ db)) ≣⟨ ─ ≀⋅≀ (─ ≀⋅≀ comm-⋅) ⟩
               ((a ⋅ c) ⋅ (da ⋅ db)) ⋅ (da ⋅ (db ⋅ dc)) ∎

          P₂ : (a ⋅ (b ⋅ dc ⋆ c ⋅ db)) ⋅ ((da ⋅ db) ⋅ (da ⋅ dc)) ∼ ((a ⋅ b) ⋅ (da ⋅ dc) ⋆ (a ⋅ c) ⋅ (da ⋅ db)) ⋅ (da ⋅ (db ⋅ dc))
          P₂ = (a ⋅ (b ⋅ dc ⋆ c ⋅ db)) ⋅ ((da ⋅ db) ⋅ (da ⋅ dc))                                   ≣⟨ distr-l-⋅ ≀⋅≀ ─ ⟩
               (a ⋅ (b ⋅ dc) ⋆ a ⋅ (c ⋅ db)) ⋅ ((da ⋅ db) ⋅ (da ⋅ dc))                              ≣⟨ distr-r-⋅ ⟩
               (a ⋅ (b ⋅ dc)) ⋅ ((da ⋅ db) ⋅ (da ⋅ dc)) ⋆ (a ⋅ (c ⋅ db)) ⋅ ((da ⋅ db) ⋅ (da ⋅ dc))    ≣⟨ P₀ ≀⋆≀ P₁ ⟩
               ((a ⋅ b) ⋅ (da ⋅ dc)) ⋅ (da ⋅ (db ⋅ dc)) ⋆ ((a ⋅ c) ⋅ (da ⋅ db)) ⋅ (da ⋅ (db ⋅ dc))    ≣⟨ distr-r-⋅ ⁻¹ ⟩
               ((a ⋅ b) ⋅ (da ⋅ dc) ⋆ (a ⋅ c) ⋅ (da ⋅ db)) ⋅ (da ⋅ (db ⋅ dc)) ∎

      in incl (⨡-MCS , P₂ ≀⋅≀ ─)

    lem-50 : ∀{a₀ a₁ b₀ b₁ : Localize R M} -> (a₀ ∼ a₁) -> (b₀ ∼ b₁) -> (a₀ ⋅-Loc b₀ ∼ a₁ ⋅-Loc b₁)
    lem-50 {a₀ / (da₀ ∢ _)} {a₁ / (da₁ ∢ _)} {b₀ / (db₀ ∢ _)} {b₁ / (db₁ ∢ _)} (incl ((s ∢ sP) , p)) (incl ((t ∢ tP) , q)) =
      let P₀ : ∀{a₀ b₀ da₁ db₁ s t} -> (a₀ ⋅ b₀) ⋅ (da₁ ⋅ db₁) ⋅ (s ⋅ t) ∼ (a₀ ⋅ da₁ ⋅ s) ⋅ (b₀ ⋅ db₁ ⋅ t)
          P₀ {a₀} {b₀} {da₁} {db₁} {s} {t} =
               (a₀ ⋅ b₀) ⋅ (da₁ ⋅ db₁) ⋅ (s ⋅ t)   ≣⟨ assoc-r-⋅ ⟩
               ((a₀ ⋅ b₀) ⋅ (da₁ ⋅ db₁) ⋅ s) ⋅ t   ≣⟨ assoc-l-⋅ ≀⋅≀ ─ ⟩
               ((a₀ ⋅ b₀) ⋅ ((da₁ ⋅ db₁) ⋅ s)) ⋅ t   ≣⟨ ─ ≀⋅≀ comm-⋅ ≀⋅≀ ─ ⟩
               ((a₀ ⋅ b₀) ⋅ (s ⋅ (da₁ ⋅ db₁))) ⋅ t   ≣⟨ ─ ≀⋅≀ (assoc-r-⋅ ∙ (comm-⋅ ≀⋅≀ ─)) ≀⋅≀ ─ ⟩
               ((a₀ ⋅ b₀) ⋅ ((da₁ ⋅ s) ⋅ db₁)) ⋅ t   ≣⟨ assoc-l-⋅ ≀⋅≀ ─ ⟩
               (a₀ ⋅ (b₀ ⋅ ((da₁ ⋅ s) ⋅ db₁))) ⋅ t   ≣⟨ ─ ≀⋅≀ assoc-r-⋅ ≀⋅≀ ─ ⟩
               (a₀ ⋅ ((b₀ ⋅ (da₁ ⋅ s)) ⋅ db₁)) ⋅ t   ≣⟨ ─ ≀⋅≀ (comm-⋅ ≀⋅≀ ─) ≀⋅≀ ─ ⟩
               (a₀ ⋅ (((da₁ ⋅ s) ⋅ b₀) ⋅ db₁)) ⋅ t   ≣⟨ ─ ≀⋅≀ assoc-l-⋅ ≀⋅≀ ─ ⟩
               (a₀ ⋅ ((da₁ ⋅ s) ⋅ (b₀ ⋅ db₁))) ⋅ t   ≣⟨ assoc-r-⋅ ≀⋅≀ ─ ⟩
               ((a₀ ⋅ (da₁ ⋅ s)) ⋅ (b₀ ⋅ db₁)) ⋅ t   ≣⟨ assoc-l-⋅ ⟩
               (a₀ ⋅ (da₁ ⋅ s)) ⋅ ((b₀ ⋅ db₁) ⋅ t)   ≣⟨ assoc-r-⋅ ≀⋅≀ ─ ⟩
               (a₀ ⋅ da₁ ⋅ s) ⋅ (b₀ ⋅ db₁ ⋅ t)     ∎

          P₁ : (a₀ ⋅ b₀) ⋅ (da₁ ⋅ db₁) ⋅ (s ⋅ t) ∼ (a₁ ⋅ b₁) ⋅ (da₀ ⋅ db₀) ⋅ (s ⋅ t)
          P₁ = P₀ ∙ (p ≀⋅≀ q) ∙ P₀ ⁻¹
      in incl (((s ∢ sP) ⋅-MCS (t ∢ tP)) , P₁)

  instance
    isSemiring:Localize : isSemiring ′ Localize R M ′
    isSemiring._⋅_ isSemiring:Localize = _⋅-Loc_
    isSemiring.⨡ isSemiring:Localize = ⨡-Loc
    isSemiring.unit-l-⋅ isSemiring:Localize = lem-20
    isSemiring.unit-r-⋅ isSemiring:Localize = lem-10 ∙ lem-20
    isSemiring.assoc-l-⋅ isSemiring:Localize = lem-30
    isSemiring.distr-l-⋅ isSemiring:Localize = lem-40
    isSemiring.distr-r-⋅ isSemiring:Localize = lem-10 ∙ lem-40 ∙ (lem-10 ≀⋆≀ lem-10)
    isSemiring._`cong-⋅`_ isSemiring:Localize = lem-50

  instance
    isRing:Localize : isRing ′ Localize R M ′
    isRing:Localize = record {}

  instance
    isCRing:Localize : isCRing ′ Localize R M ′
    isCRing.comm-⋅ isCRing:Localize = lem-10



