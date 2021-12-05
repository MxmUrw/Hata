
module Verification.Core.Theory.Std.Specific.MetaTermCalculus2.Pattern.Instance.PrincipalFamilyCat where

open import Verification.Core.Conventions hiding (Structure)
open import Verification.Core.Set.Decidable
open import Verification.Core.Set.Discrete
open import Verification.Core.Set.Contradiction
-- open import Verification.Core.Set.Setoid.Definition
open import Verification.Core.Set.Setoid.Morphism
-- open import Verification.Core.Algebra.Monoid.Definition
open import Verification.Core.Algebra.Monoid.Free
-- open import Verification.Core.Data.List.Variant.Binary.Element
open import Verification.Core.Data.Universe.Everything hiding (isCategory:𝒰)
open import Verification.Core.Data.Product.Definition
open import Verification.Core.Data.List.Variant.Unary.Definition
open import Verification.Core.Data.Nat.Free
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
open import Verification.Core.Category.Std.Morphism.EpiMono
open import Verification.Core.Category.Std.Morphism.Iso
open import Verification.Core.Category.Std.Limit.Specific.Coproduct.Definition
-- open import Verification.Core.Category.Std.Limit.Specific.Coequalizer
open import Verification.Core.Category.Std.Functor.RelativeAdjoint

open import Verification.Core.Data.Indexed.Definition
-- open import Verification.Core.Data.Indexed.Instance.Monoid
open import Verification.Core.Data.FiniteIndexed.Definition
open import Verification.Core.Data.FiniteIndexed.Property.Adjunction
-- open import Verification.Core.Data.Renaming.Definition
open import Verification.Core.Data.Substitution.Definition
-- open import Verification.Core.Data.Renaming.Instance.CoproductMonoidal
-- open import Verification.Core.Category.Std.Category.Subcategory.Full

open import Verification.Core.Theory.Std.Specific.MetaTermCalculus2.Pattern.Definition
open import Verification.Core.Theory.Std.Specific.MetaTermCalculus2.Pattern.Instance.Category
-- open import Verification.Core.Theory.Std.Specific.MetaTermCalculus2.Pattern.Instance.FiniteCoproductCategory

open import Verification.Core.Computation.Unification.Monoidic.PrincipalFamilyCat2
open import Verification.Core.Order.WellFounded.Definition
open import Verification.Core.Order.Preorder 
open import Verification.Core.Order.Lattice hiding (⊥)
open import Verification.Core.Computation.Unification.Definition
-- open import Verification.Core.Computation.Unification.Monoidic.PrincipalFamily
-- open import Verification.Core.Computation.Unification.Monoidic.ToCoequalizer
-- open import Verification.Core.Algebra.Monoid.Definition
-- open import Verification.Core.Algebra.MonoidWithZero.Definition
-- open import Verification.Core.Algebra.MonoidWithZero.Ideal
-- open import Verification.Core.Algebra.MonoidAction.Definition

open import Verification.Core.Theory.Std.Specific.MetaTermCalculus2.Pattern.Instance.PCF.Base
open import Verification.Core.Theory.Std.Specific.MetaTermCalculus2.Pattern.Instance.PCF.SuccessRigidRigid





module _ {K : Kinding 𝑖} {{_ : isMetaTermCalculus 𝑖 K}} where


    ∂-𝐏𝐚𝐭 : ∀{x y : 𝐏𝐚𝐭 K} -> (i : Pair x y)
           -> (isBase-𝐏𝐚𝐭 i
              +-𝒰 (∑ λ n -> isSplittableC (𝐏𝐚𝐭 K) n i SplitP))

    -- if the domain is empty, we reached a base case
    -- ∂-𝐏𝐚𝐭 {incl ◌-⧜} {y} (f , g) = left empty-domain

    -- if the domain is not a singleton, we can split it
    -- ∂-𝐏𝐚𝐭 {incl (x ⋆-⧜ y)} {z} ((fx ⋆-⧜ fy) , (gx ⋆-⧜ gy)) =
    --   right (2 , record
    --              { famC      = mfam
    --              ; coversC   = {!!}
    --              ; fampropsC = {!!}
    --              })
    --     where
    --       mfam : 2 ∍ tt -> _
    --       mfam (left-∍ incl)  = incl x , (fx , gx)
    --       mfam (right-∍ (left-∍ incl)) = incl y , (fy , gy)

    ------------------------------------------------------------
    -- if the domain is a singleton, we look at the values of f and g at this singleton

    -----------------------
    -- case rigid - rigid

    -- var ≠ con
    -- ∂-𝐏𝐚𝐭 {incl _} (incl (app-var x tsx) , incl (app-con x₂ tsy)) = left (no-unification (lem-20-var-con {ts = tsx} {ts' = tsy}))

    -- con ≠ var
    -- ∂-𝐏𝐚𝐭 {incl _} (incl (app-con x x₁) , incl (app-var x₂ x₃)) = {!!}


    -- var = var
    -- ∂-𝐏𝐚𝐭 {incl _} {𝔍} (incl (app-var {Γ = Γ} {Δ = Δx} vx (tsx)) , incl (app-var {Δ = Δy} vy (tsy))) with Δx ≟-Str Δy
    -- ... | no ¬p = left (no-unification (lem-20-var-var {ts = tsx} {ts' = tsy} ¬p))
    -- ... | yes refl-≣ with vx ≟-Str vy
    -- ... | no ¬p = left (no-unification (lem-20-var-var' {ts = tsx} {ts' = tsy} ¬p))
    -- ... | yes refl-≣ = right (1 , success-var-var vx (tsx) (tsy))

    -- con = con
    -- ∂-𝐏𝐚𝐭 {incl _} (incl (app-con x x₁) , incl (app-con x₂ x₃)) = {!!}

    -----------------------
    -- case flex - flex

    ∂-𝐏𝐚𝐭 {incl _} (incl (app-meta {Δ = Δx} Mx tsx) , incl (app-meta {Δ = Δy} My tsy)) with (Δx ≟-Str Δy)
    ... | yes p = {!!}
    ... | no ¬p = {!!}
    -- with Mx ≟-Str My
    -- ... | X = ?

    -----------------------
    -- case flex - rigid
    -- ∂-𝐏𝐚𝐭 {incl _} (incl (app-meta M s) , incl (app-var x x₁)) = {!!}
    -- ∂-𝐏𝐚𝐭 {incl _} (incl (app-meta M s) , incl (app-con x x₁)) = {!!}
    -- ∂-𝐏𝐚𝐭 {incl _} (incl (app-var x x₁) , incl (app-meta M s)) = {!!}
    -- ∂-𝐏𝐚𝐭 {incl _} (incl (app-con x x₁) , incl (app-meta M s)) = {!!}
    ∂-𝐏𝐚𝐭 {incl _} _ = {!!} --

{-

    -- if the domain is not a singleton, we can split it
    ∂-𝐏𝐚𝐭 {incl (incl (a ⋆-⧜ b))} {y} (f , g) =
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
    ∂-𝐏𝐚𝐭 {incl (incl ◌-⧜)} {y} (f , g) = left ({!!})

    -- if the domain is a singleton, we look at the values of f and g at this singleton
    ∂-𝐏𝐚𝐭 {incl (incl (incl x))} {y} (f , g) with (⟨ f ⟩ x incl) in fp | (⟨ g ⟩ x incl) in gp
    ... | app-meta M s | app-meta M₁ s₁ = {!!}
    ... | app-meta M s | app-var x x₁   = {!!}
    ... | app-meta M s | app-con x x₁   = {!!}
    ... | app-var x x₁ | app-meta M s   = {!!}
    ... | app-var {Δ = Δ₀} v₀ ts₀ | app-var {Δ = Δ₁} v₁ ts₁  with Δ₀ ≟-Str Δ₁
    ... | yes refl-≣ = {!!}
    ... | no ¬p = left (no-unification {t = app-var v₀ ts₀} (lem-20-var-var ¬p) (incl (λ {i i₁ incl → (≡-Str→≡ fp i₁) })) {!!})
    -- ... | no ¬p = left (no-unification {t = app-var v₀ ts₀} {s = app-var {Δ = Δ₁} v₁ ts₁} (lem-20-var-var ¬p) (incl (λ {i i₁ incl → (≡-Str→≡ fp i₁) })) {!!})
    ∂-𝐏𝐚𝐭 {incl (incl (incl x))} {y} (f , g) | app-var v ts₀ | app-con c ts₁  =
      left (no-unification {t = app-var v ts₀} {s = app-con c ts₁} (lem-20-var-con) (incl (λ {i i₁ incl → (≡-Str→≡ fp i₁) })) {!!})
    ∂-𝐏𝐚𝐭 {incl (incl (incl x))} {y} (f , g) | app-con c x₁ | app-meta M s   = {!!}
    ∂-𝐏𝐚𝐭 {incl (incl (incl x))} {y} (f , g) | app-con c x₁ | app-var x₂ x₃  = {!!}
    ∂-𝐏𝐚𝐭 {incl (incl (incl x))} {y} (f , g) | app-con c x₁ | app-con x₂ x₃  = {!!}

  instance
    isPrincipalFamilyCat:𝐏𝐚𝐭 : isPrincipalFamilyCat (𝐏𝐚𝐭 K)
    isPrincipalFamilyCat.SizeC isPrincipalFamilyCat:𝐏𝐚𝐭         = 𝒲
    isPrincipalFamilyCat.isBase isPrincipalFamilyCat:𝐏𝐚𝐭        = isBase-𝐏𝐚𝐭
    isPrincipalFamilyCat.sizeC isPrincipalFamilyCat:𝐏𝐚𝐭         = msize
    isPrincipalFamilyCat.∂C isPrincipalFamilyCat:𝐏𝐚𝐭            = ∂-𝐏𝐚𝐭
    isPrincipalFamilyCat.size0 isPrincipalFamilyCat:𝐏𝐚𝐭         = {!!}
    isPrincipalFamilyCat.initial-size0 isPrincipalFamilyCat:𝐏𝐚𝐭 = {!!}
    isPrincipalFamilyCat.isPrincipalC:Base isPrincipalFamilyCat:𝐏𝐚𝐭 f g x = {!!}

-}
