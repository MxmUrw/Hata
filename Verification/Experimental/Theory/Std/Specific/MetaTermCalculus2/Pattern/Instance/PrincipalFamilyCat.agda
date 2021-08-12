
module Verification.Experimental.Theory.Std.Specific.MetaTermCalculus2.Pattern.Instance.PrincipalFamilyCat where

open import Verification.Experimental.Conventions hiding (Structure)
open import Verification.Experimental.Set.Decidable
open import Verification.Experimental.Set.Discrete
open import Verification.Experimental.Set.Contradiction
open import Verification.Experimental.Set.Setoid.Definition
open import Verification.Experimental.Algebra.Monoid.Definition
open import Verification.Experimental.Algebra.Monoid.Free
open import Verification.Experimental.Algebra.Monoid.Free.Element
open import Verification.Experimental.Data.Universe.Everything
open import Verification.Experimental.Data.Product.Definition
-- open import Verification.Experimental.Theory.Std.Generic.TypeTheory.Definition
-- open import Verification.Experimental.Theory.Std.Generic.TypeTheory.Simple
-- open import Verification.Experimental.Theory.Std.Generic.TypeTheory.Simple.Judgement2
open import Verification.Experimental.Theory.Std.TypologicalTypeTheory.CwJ.Definition
-- open import Verification.Experimental.Theory.Std.Generic.TypeTheory.Simple

open import Verification.Experimental.Category.Std.Category.Definition
open import Verification.Experimental.Category.Std.Category.As.Monoid
open import Verification.Experimental.Category.Std.Category.Structured.Monoidal.Definition
open import Verification.Experimental.Category.Std.Functor.Definition
open import Verification.Experimental.Category.Std.RelativeMonad.Definition
open import Verification.Experimental.Category.Std.RelativeMonad.KleisliCategory.Definition
open import Verification.Experimental.Category.Std.Category.Subcategory.Definition
open import Verification.Experimental.Category.Std.Morphism.EpiMono
open import Verification.Experimental.Category.Std.Morphism.Iso
open import Verification.Experimental.Category.Std.Limit.Specific.Coproduct.Definition
open import Verification.Experimental.Category.Std.Limit.Specific.Coequalizer

open import Verification.Experimental.Data.Indexed.Definition
open import Verification.Experimental.Data.Indexed.Instance.Monoid
open import Verification.Experimental.Data.FiniteIndexed.Definition
open import Verification.Experimental.Data.Renaming.Definition
open import Verification.Experimental.Data.Renaming.Instance.CoproductMonoidal

open import Verification.Experimental.Theory.Std.Specific.MetaTermCalculus2.Pattern.Definition
open import Verification.Experimental.Theory.Std.Specific.MetaTermCalculus2.Pattern.Instance.Category
open import Verification.Experimental.Theory.Std.Specific.MetaTermCalculus2.Pattern.Instance.FiniteCoproductCategory

open import Verification.Experimental.Computation.Unification.Monoidic.PrincipalFamilyCat2
open import Verification.Experimental.Order.WellFounded.Definition
open import Verification.Experimental.Order.Preorder 
open import Verification.Experimental.Order.Lattice hiding (⊥)
open import Verification.Experimental.Computation.Unification.Definition
open import Verification.Experimental.Computation.Unification.Monoidic.PrincipalFamily
-- open import Verification.Experimental.Computation.Unification.Monoidic.ToCoequalizer
open import Verification.Experimental.Algebra.Monoid.Definition
-- open import Verification.Experimental.Algebra.MonoidWithZero.Definition
-- open import Verification.Experimental.Algebra.MonoidWithZero.Ideal
-- open import Verification.Experimental.Algebra.MonoidAction.Definition

ap : ∀{A : 𝒰 𝑖} {B : 𝒰 𝑗} -> {f g : A -> B} -> (f ≡ g) -> (a : A) -> f a ≡ g a
ap p a i = p i a


private
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
    single : ∀{a : Jdg₂ ⟨ K ⟩} {b : 𝐏𝐚𝐭 K} -> (t : ⟨ ⟨ b ⟩ ⟩ ⊩ᶠ-pat a) -> incl (incl (incl a)) ⟶ b
    single t = incl (λ {i incl → t})

  instance
    isDiscrete:𝐏𝐚𝐭 : isDiscrete (𝐏𝐚𝐭 K)
    isDiscrete:𝐏𝐚𝐭 = {!!}

  instance
    isSet-Str:𝐏𝐚𝐭 : isSet-Str (𝐏𝐚𝐭 K)
    isSet-Str:𝐏𝐚𝐭 = {!!}

  private
    data isBase-𝐏𝐚𝐭 : {a b : 𝐏𝐚𝐭 K} -> Pair a b -> 𝒰 𝑖 where
      empty-domain : ∀{b : 𝐏𝐚𝐭 K} -> {σ ρ : ⊥ ⟶ b} -> isBase-𝐏𝐚𝐭 (σ , ρ)
      no-unification : ∀{a : Jdg₂ ⟨ K ⟩} {b : 𝐏𝐚𝐭 K} -> {t s : ⟨ ⟨ b ⟩ ⟩ ⊩ᶠ-pat a} -> (∀{c} -> (σ : b ⟶ c) -> subst-𝐏𝐚𝐭 t σ ≣ subst-𝐏𝐚𝐭 s σ -> ⊥-𝒰 {ℓ₀})
                      -> {f g : incl (incl (incl a)) ⟶ b}
                      -> f ∼ single t -> g ∼ single s
                      -> isBase-𝐏𝐚𝐭 (f , g)

    lem-10 : ∀{a b : 𝐏𝐚𝐭 K} -> (f g : a ⟶ b) -> isBase-𝐏𝐚𝐭 (f , g) -> isDecidable (hasCoequalizer f g)
    lem-10 f g empty-domain = right (hasCoequalizer:byInitial f g)
    lem-10 f g (no-unification {a} {b} {t} {s} p {f} {g} fp gp) = left {!!} -- P
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
              -> {x : Γ ∍ (Δ ⇒ α)}     -> {ts : ∀ {i} -> Δ ∍ i -> ⟨ ⟨ j ⟩ ⟩ ⊩ᶠ-patlam (Γ ∥ i)}
              -> {c : TermCon (Δ' ⇒ α)} -> {ts' : ∀ {i} -> Δ' ∍ i -> ⟨ ⟨ j ⟩ ⟩ ⊩ᶠ-patlam (Γ ∥ i)}
              -> ∀{k} -> (σ : j ⟶ k)
              -> subst-𝐏𝐚𝐭 (app-var x ts) σ ≣ subst-𝐏𝐚𝐭 (app-con c ts') σ
              -> ⊥-𝒰 {ℓ₀}
    lem-20-var-con σ ()

    lem-20-var-var : ∀{Γ Δ Δ' α} {j : 𝐏𝐚𝐭 K}
              -> {x : Γ ∍ (Δ ⇒ α)}     -> {ts : ∀ {i} -> Δ ∍ i -> ⟨ ⟨ j ⟩ ⟩ ⊩ᶠ-patlam (Γ ∥ i)}
              -> {x' : Γ ∍ (Δ' ⇒ α)}     -> {ts' : ∀ {i} -> Δ' ∍ i -> ⟨ ⟨ j ⟩ ⟩ ⊩ᶠ-patlam (Γ ∥ i)}
              -> ∀{k} -> (σ : j ⟶ k)
              -> Δ ≢-Str Δ'
              -> subst-𝐏𝐚𝐭 (app-var x ts) σ ≣ subst-𝐏𝐚𝐭 (app-var x' ts') σ
              -> ⊥-𝒰 {ℓ₀}
    lem-20-var-var {Δ = Δ} {Δ'} σ q p =
      let p' : Δ ≡ Δ'
          p' = cancel-injective-app-var (≡-Str→≡ p) .fst
      in impossible (q (≡→≡-Str p'))

      -- app-con : ∀{𝔍 Γ Δ α}
      --         -> TermCon (Δ ⇒ α) -> (∀ {i} -> Δ ∍ i -> 𝔍 ⊩ᶠ-patlam (Γ ∥ i))
      --         -> 𝔍 ⊩ᶠ-pat (Γ ⇒ α)

    postulate
      msize : ∀{a b : 𝐏𝐚𝐭 K} -> Pair a b -> 𝒲

    ∂-𝐏𝐚𝐭 : ∀{x y : 𝐏𝐚𝐭 K} -> (i : Pair x y)
           -> (isBase-𝐏𝐚𝐭 i
              +-𝒰 (∑ λ n -> isSplittableC (𝐏𝐚𝐭 K) n (x , y , i) (λ (_ , _ , j) -> msize j ≪-𝒲 msize i)))

    -- if the domain is not a singleton, we can split it
    ∂-𝐏𝐚𝐭 {incl (incl (a ⋆-Free-𝐌𝐨𝐧 b))} {y} (f , g) =
      right (2 , record
                 { famC      = mfam
                 ; coversC   = {!!}
                 ; fampropsC = {!!}
                 })
        where
          f₀ g₀ : incl (incl a) ⟶ y
          f₀ = incl (λ i x → ⟨ f ⟩ i (left-∍ x))
          g₀ = incl (λ i x → ⟨ g ⟩ i (left-∍ x))

          f₁ g₁ : incl (incl b) ⟶ y
          f₁ = incl (λ i x → ⟨ f ⟩ i (right-∍ x))
          g₁ = incl (λ i x → ⟨ g ⟩ i (right-∍ x))

          mfam : Fin-R 2 -> _
          mfam zero = incl (incl a) , y , (f₀ , g₀)
          mfam (suc zero) = incl (incl b) , y , (f₁ , g₁)

    -- if the domain is empty, we reached a base case
    ∂-𝐏𝐚𝐭 {incl (incl ◌-Free-𝐌𝐨𝐧)} {y} (f , g) = left ({!!})

    -- if the domain is a singleton, we look at the values of f and g at this singleton
    ∂-𝐏𝐚𝐭 {incl (incl (incl x))} {y} (f , g) with (⟨ f ⟩ x incl) in fp | (⟨ g ⟩ x incl) in gp
    ... | app-meta M s | app-meta M₁ s₁ = {!!}
    ... | app-meta M s | app-var x x₁   = {!!}
    ... | app-meta M s | app-con x x₁   = {!!}
    ... | app-var x x₁ | app-meta M s   = {!!}
    ... | app-var x x₁ | app-var x₂ x₃  = {!!}
    ... | app-var x x₁ | app-con x₂ x₃  = left (no-unification {t = app-var x x₁} {s = app-con x₂ x₃} (lem-20-var-con) (incl (λ {i i₁ incl → (≡-Str→≡ fp i₁) })) {!!})
    ... | app-con x x₁ | app-meta M s   = {!!}
    ... | app-con x x₁ | app-var x₂ x₃  = {!!}
    ... | app-con x x₁ | app-con x₂ x₃  = {!!}

  instance
    isPrincipalFamilyCat:𝐏𝐚𝐭 : isPrincipalFamilyCat (𝐏𝐚𝐭 K)
    isPrincipalFamilyCat.SizeC isPrincipalFamilyCat:𝐏𝐚𝐭         = 𝒲
    isPrincipalFamilyCat.isBase isPrincipalFamilyCat:𝐏𝐚𝐭        = isBase-𝐏𝐚𝐭
    isPrincipalFamilyCat.sizeC isPrincipalFamilyCat:𝐏𝐚𝐭         = msize
    isPrincipalFamilyCat.∂C isPrincipalFamilyCat:𝐏𝐚𝐭            = ∂-𝐏𝐚𝐭
    isPrincipalFamilyCat.size0 isPrincipalFamilyCat:𝐏𝐚𝐭         = {!!}
    isPrincipalFamilyCat.initial-size0 isPrincipalFamilyCat:𝐏𝐚𝐭 = {!!}
    isPrincipalFamilyCat.isPrincipalC:Base isPrincipalFamilyCat:𝐏𝐚𝐭 f g x = {!!}

{-
-}
