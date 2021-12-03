
module Verification.Core.Theory.Std.Specific.MetaTermCalculus2.Pattern.Instance.PrincipalFamilyCatBase where

open import Verification.Core.Conventions hiding (Structure)
open import Verification.Core.Set.Decidable
open import Verification.Core.Set.Discrete
open import Verification.Core.Set.Contradiction
open import Verification.Core.Set.Setoid.Definition
open import Verification.Core.Algebra.Monoid.Definition
open import Verification.Core.Algebra.Monoid.Free
open import Verification.Core.Data.List.Variant.FreeMonoid.Element
open import Verification.Core.Data.Universe.Everything
open import Verification.Core.Data.Product.Definition
open import Verification.Core.Data.List.Variant.Base.Definition
-- open import Verification.Core.Theory.Std.Generic.TypeTheory.Definition
-- open import Verification.Core.Theory.Std.Generic.TypeTheory.Simple
-- open import Verification.Core.Theory.Std.Generic.TypeTheory.Simple.Judgement2
open import Verification.Core.Theory.Std.TypologicalTypeTheory.CwJ.Kinding
-- open import Verification.Core.Theory.Std.Generic.TypeTheory.Simple

open import Verification.Core.Category.Std.Category.Definition
-- open import Verification.Core.Category.Std.Category.As.Monoid
-- open import Verification.Core.Category.Std.Category.Structured.Monoidal.Definition
open import Verification.Core.Category.Std.Functor.Definition
open import Verification.Core.Category.Std.RelativeMonad.Definition
open import Verification.Core.Category.Std.RelativeMonad.KleisliCategory.Definition
open import Verification.Core.Category.Std.Category.Subcategory.Definition
-- open import Verification.Core.Category.Std.Morphism.EpiMono
open import Verification.Core.Category.Std.Morphism.Iso
open import Verification.Core.Category.Std.Limit.Specific.Coproduct.Definition
open import Verification.Core.Category.Std.Limit.Specific.Coequalizer

open import Verification.Core.Data.Indexed.Definition
open import Verification.Core.Data.Indexed.Instance.Monoid
open import Verification.Core.Data.FiniteIndexed.Definition
open import Verification.Core.Data.Renaming.Definition
open import Verification.Core.Data.Substitution.Definition
open import Verification.Core.Data.Renaming.Instance.CoproductMonoidal

open import Verification.Core.Theory.Std.Specific.MetaTermCalculus2.Pattern.Definition
open import Verification.Core.Theory.Std.Specific.MetaTermCalculus2.Pattern.Instance.Category
open import Verification.Core.Theory.Std.Specific.MetaTermCalculus2.Pattern.Instance.FiniteCoproductCategory

open import Verification.Core.Computation.Unification.Monoidic.PrincipalFamilyCat2
open import Verification.Core.Order.WellFounded.Definition
open import Verification.Core.Order.Preorder 
open import Verification.Core.Order.Lattice hiding (⊥)
open import Verification.Core.Computation.Unification.Definition
-- open import Verification.Core.Computation.Unification.Monoidic.PrincipalFamily
-- open import Verification.Core.Computation.Unification.Monoidic.ToCoequalizer
open import Verification.Core.Algebra.Monoid.Definition
-- open import Verification.Core.Algebra.MonoidWithZero.Definition
-- open import Verification.Core.Algebra.MonoidWithZero.Ideal
-- open import Verification.Core.Algebra.MonoidAction.Definition

ap : ∀{A : 𝒰 𝑖} {B : 𝒰 𝑗} -> {f g : A -> B} -> (f ≡ g) -> (a : A) -> f a ≡ g a
ap p a i = p i a


mWF : 𝒰₀
mWF = ℕ ^ 3

macro 𝒲 = #structureOn mWF

postulate
  _≪-𝒲_ : 𝒲 -> 𝒲 -> 𝒰 ℓ₀
  WellFounded-≪-𝒲 : WellFounded _≪-𝒲_


instance
  isWellfounded:mWF : isWF {ℓ₀} ℓ₀ 𝒲
  isWellfounded:mWF = record { _≪_ = _≪-𝒲_ ; wellFounded = WellFounded-≪-𝒲 }

instance
  isWFT:mWF : isWFT 𝒲
  isWFT:mWF = {!!}




module _ {K : Kinding 𝑖} {{_ : isMetaTermCalculus 𝑖 K}} where

  -- coeq-𝐏𝐚𝐭 : (a b : 𝐏𝐚𝐭 K) -> 𝐏𝐚𝐭 K
  -- coeq-𝐏𝐚𝐭 = {!!}

  private
    single : ∀{a : Jdg₂ ⟨ K ⟩} {b : 𝐏𝐚𝐭 K} -> (t : ⟨ b ⟩ ⊩ᶠ-pat a) -> incl (incl a) ⟶ b
    single t = incl t
    -- incl (λ {i incl → t})

  instance
    isDiscrete:𝐏𝐚𝐭 : isDiscrete (𝐏𝐚𝐭 K)
    isDiscrete:𝐏𝐚𝐭 = {!!}

  instance
    isSet-Str:𝐏𝐚𝐭 : isSet-Str (𝐏𝐚𝐭 K)
    isSet-Str:𝐏𝐚𝐭 = {!!}

  data isBase-𝐏𝐚𝐭 : {a b : 𝐏𝐚𝐭 K} -> Pair a b -> 𝒰 𝑖 where
    empty-domain : ∀{b : 𝐏𝐚𝐭 K} -> {σ ρ : ⊥ ⟶ b} -> isBase-𝐏𝐚𝐭 (σ , ρ)
    no-unification : ∀{a : Jdg₂ ⟨ K ⟩} {b : 𝐏𝐚𝐭 K} -> {t s : ⟨ b ⟩ ⊩ᶠ-pat a} -> (∀{c} -> (σ : b ⟶ c) -> subst-⧜𝐒𝐮𝐛𝐬𝐭 σ t ≣ subst-⧜𝐒𝐮𝐛𝐬𝐭 σ s -> ⊥-𝒰 {ℓ₀})
                    -> isBase-𝐏𝐚𝐭 (incl t , incl s)

  lem-10 : ∀{a b : 𝐏𝐚𝐭 K} -> (f g : a ⟶ b) -> isBase-𝐏𝐚𝐭 (f , g) -> isDecidable (hasCoequalizer f g)
  lem-10 = {!!}

    -- lem-10 f g empty-domain = right (hasCoequalizer:byInitial f g)
    -- lem-10 f g (no-unification {a} {b} {t} {s} p {f} {g} fp gp) = left {!!} -- P
      -- where
      --   P : hasCoequalizer f g -> 𝟘-𝒰
      --   P (e since eP) =
      --     let P₀ = ∼-Coeq

      --              >> f ◆ π-Coeq ∼ g ◆ π-Coeq <<

      --              ⟪ ( λ q -> ap (⟨ q ⟩ a) incl ) ⟫

      --              >> subst-𝐏𝐚𝐭 t π-Coeq ≡ subst-𝐏𝐚𝐭 s π-Coeq <<

      --              ⟪ ≡→≡-Str ⟫

      --              >> subst-𝐏𝐚𝐭 t π-Coeq ≣ subst-𝐏𝐚𝐭 s π-Coeq <<

      --              ⟪ p π-Coeq ⟫

      --              >> ⊥-𝒰 <<

      --     in impossible P₀


  lem-20-var-con : ∀{Γ Δ Δ' α} {j : 𝐏𝐚𝐭 K}
            -> {x : ι Γ ∍ (Δ ⇒ α)}     -> {ts : Pat-pats ⟨ j ⟩ Γ (ι Δ)} -- {ts : ∀ {i} -> ι Δ ∍ i -> ⟨ j ⟩ ⊩ᶠ-patlam (Γ ∥ i)}
            -> {c : TermCon (Δ' ⇒ α)}  -> {ts' : Pat-pats ⟨ j ⟩ Γ (ι Δ')} -- {ts' : ∀ {i} -> ι Δ' ∍ i -> ⟨ j ⟩ ⊩ᶠ-patlam (Γ ∥ i)}
            -> ∀{k} -> (σ : j ⟶ k)
            -> subst-⧜𝐒𝐮𝐛𝐬𝐭 σ (app-var x ts) ≣ subst-⧜𝐒𝐮𝐛𝐬𝐭 σ (app-con c ts')
            -- -> subst-⧜𝐒𝐮𝐛𝐬𝐭 σ (app-var x ts) σ ≣ subst-𝐏𝐚𝐭 (app-con c ts') σ
            -> ⊥-𝒰 {ℓ₀}
  lem-20-var-con {ts = lam x} {ts' = lam x₁} σ ()

  lem-20-var-var : ∀{Γ Δ Δ' α} {j : 𝐏𝐚𝐭 K}
            -> {x : ι Γ ∍ (Δ ⇒ α)}    -> {ts : Pat-pats ⟨ j ⟩ Γ (ι Δ)}   --  -> {ts : ∀ {i} -> ι Δ ∍ i -> ⟨ j ⟩ ⊩ᶠ-patlam (Γ ∥ i)}
            -> {x' : ι Γ ∍ (Δ' ⇒ α)}  -> {ts' : Pat-pats ⟨ j ⟩ Γ (ι Δ')} --  -> {ts' : ∀ {i} -> ι Δ' ∍ i -> ⟨ j ⟩ ⊩ᶠ-patlam (Γ ∥ i)}
            -> Δ ≢-Str Δ'
            -> ∀{k} -> (σ : j ⟶ k)
            -> subst-⧜𝐒𝐮𝐛𝐬𝐭 σ (app-var x ts) ≣ subst-⧜𝐒𝐮𝐛𝐬𝐭 σ (app-var x' ts')
            -> ⊥-𝒰 {ℓ₀}
  lem-20-var-var {Δ = Δ} {Δ'} q σ p = {!!}
    -- let p' : Δ ≡ Δ'
    --     p' = cancel-injective-app-var (≡-Str→≡ p) .fst
    -- in impossible (q (≡→≡-Str p'))

  lem-20-var-var' : ∀{Γ Δ α} {j : 𝐏𝐚𝐭 K}
            -> {x : ι Γ ∍ (Δ ⇒ α)}    -> {ts : Pat-pats ⟨ j ⟩ Γ (ι Δ)}   --    -> {ts : ∀ {i} -> ι Δ ∍ i -> ⟨ j ⟩ ⊩ᶠ-patlam (Γ ∥ i)}
            -> {x' : ι Γ ∍ (Δ ⇒ α)}   -> {ts' : Pat-pats ⟨ j ⟩ Γ (ι Δ)} --     -> {ts' : ∀ {i} -> ι Δ ∍ i -> ⟨ j ⟩ ⊩ᶠ-patlam (Γ ∥ i)}
            -> x ≢-Str x'
            -> ∀{k} -> (σ : j ⟶ k)
            -> subst-⧜𝐒𝐮𝐛𝐬𝐭 σ (app-var x ts) ≣ subst-⧜𝐒𝐮𝐛𝐬𝐭 σ (app-var x' ts')
            -> ⊥-𝒰 {ℓ₀}
  lem-20-var-var' {Δ = Δ} q σ p = {!!}
    -- let p' : Δ ≡ Δ'
    --     p' = cancel-injective-app-var (≡-Str→≡ p) .fst
    -- in impossible (q (≡→≡-Str p'))

    -- app-con : ∀{𝔍 Γ Δ α}
    --         -> TermCon (Δ ⇒ α) -> (∀ {i} -> Δ ∍ i -> 𝔍 ⊩ᶠ-patlam (Γ ∥ i))
    --         -> 𝔍 ⊩ᶠ-pat (Γ ⇒ α)

  postulate
    msize : ∀{a b : 𝐏𝐚𝐭 K} -> Pair a b -> 𝒲

{-
-}

