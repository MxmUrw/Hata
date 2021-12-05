
module Verification.Core.Theory.Std.Specific.MetaTermCalculus2.Pattern.Definition where

open import Verification.Core.Conventions hiding (Structure)
open import Verification.Core.Algebra.Monoid.Definition
open import Verification.Core.Algebra.Monoid.Free
open import Verification.Core.Data.List.Variant.Binary.Element
open import Verification.Core.Order.Lattice
open import Verification.Core.Data.Universe.Everything
open import Verification.Core.Data.Product.Definition
open import Verification.Core.Category.Std.Category.Definition
-- open import Verification.Core.Theory.Std.Generic.TypeTheory.Definition
open import Verification.Core.Theory.Std.Generic.TypeTheory.Simple
open import Verification.Core.Theory.Std.Generic.TypeTheory.Simple.Judgement2
open import Verification.Core.Theory.Std.TypologicalTypeTheory.CwJ.Kinding
open import Verification.Core.Category.Std.Category.Structured.Monoidal.Definition
open import Verification.Core.Category.Std.Functor.Definition
open import Verification.Core.Theory.Std.Generic.TypeTheory.Simple
open import Verification.Core.Set.Function.Injective

open import Verification.Core.Data.Indexed.Definition
open import Verification.Core.Data.Indexed.Instance.Monoid
open import Verification.Core.Data.FiniteIndexed.Definition
open import Verification.Core.Data.FiniteIndexed.Property.Adjunction
open import Verification.Core.Data.NormalFiniteIndexed.Definition
open import Verification.Core.Data.Renaming.Definition
open import Verification.Core.Data.Renaming.Instance.CoproductMonoidal

open import Verification.Core.Category.Std.Morphism.EpiMono
open import Verification.Core.Category.Std.Category.Subcategory.Definition
open import Verification.Core.Category.Std.Functor.RelativeAdjoint



module _ {K : 𝒰 𝑖} (R : List K -> K -> 𝒰 𝑗) where
  data Subs : (Γ : (List K)) -> (Δ : List K) -> 𝒰 (𝑖 ､ 𝑗) where
    [] : ∀{Γ} -> Subs Γ []
    _∷_ : ∀{Γ Δ k} -> R Γ k -> Subs Γ Δ -> Subs Γ (k ∷ Δ)

module _ {K : 𝒰 𝑖} {R : List K -> K -> 𝒰 𝑗} where
  getvar : ∀{Γ Δ k} -> Subs R Γ Δ -> Δ ⊨-var k -> R Γ k
  getvar (x ∷ s) zero = x
  getvar (x ∷ s) (suc i) = getvar s i


record Jdg₂ (A : 𝒰 𝑖) : 𝒰 𝑖 where
  inductive
  constructor _⇒_
  -- field fst : ⋆List (Jdg₂ A)
  field fst : List (Jdg₂ A)
  field snd : A
infix 4 _⇒_

open Jdg₂ public

module _ {A : 𝒰 𝑖} where
  instance
    isDiscrete:Jdg₂ : {{isDiscrete A}} -> isDiscrete (Jdg₂ A)
    isDiscrete:Jdg₂ = {!!}

record Jdg₃ (A : 𝒰 𝑖) : 𝒰 𝑖 where
  constructor _∥_
  -- field fst : ⋆List (Jdg₂ A)
  field fst : List (Jdg₂ A)
  field snd : Jdg₂ A
infix 4 _∥_

open Jdg₃ public

record isMetaTermCalculus (𝑖 : 𝔏) {𝑗} (K : Kinding 𝑗) : 𝒰 (𝑗 ⁺ ､ 𝑖 ⁺) where
  field TermCon : Jdg₂ ⟨ K ⟩ -> 𝒰 (𝑖)

open isMetaTermCalculus {{...}} public

MetaTermCalculus : (𝑖 : 𝔏 ^ 2) -> 𝒰 _
MetaTermCalculus 𝑖 = _ :& isMetaTermCalculus (𝑖 ⌄ 0) {𝑖 ⌄ 1}


module _ {K' : Kinding _} {{_ : isMetaTermCalculus 𝑖 {𝑖} K'}} where

  -- jdg₂ : Jdg₃ K -> Jdg₂ K
  -- jdg₂ (Γ ∥ (Δ ⇒ α)) = Γ ⋆ Δ ⇒ α

  -- 𝒞 : Category _
  -- 𝒞 = 𝐅𝐚𝐦 (𝐔𝐧𝐢𝐯 𝑖) 𝑖
  private
    K = ⟨ K' ⟩

    -- (Jdg₂ ⟨ K' ⟩) = Jdg₂ K


  InjVars : Category _
  -- InjVars = 𝐒𝐮𝐛ₘₒₙₒ (𝐅𝐢𝐧𝐈𝐱 (Jdg₂ K))
  InjVars = ♮𝐑𝐞𝐧 (Jdg₂ ⟨ K' ⟩)
  -- 𝐒𝐮𝐛ₘₒₙₒ (♮𝐅𝐢𝐧𝐈𝐱 (Jdg₂ K))


  injVars : List (Jdg₂ K) -> List (Jdg₂ K) -> 𝒰 _
  injVars a b = Hom {{of InjVars}} (incl (incl a)) (incl (incl b))

  -- injVars : ⋆List (Jdg₂ K) -> ⋆List (Jdg₂ K) -> 𝒰 _
  -- injVars a b = Hom {{of InjVars}} (incl (incl a)) (incl (incl b))

  -- injVars Γ Δ = ∑ λ (f : ∀ {i} -> (Δ ∍ i) -> (Γ ∍ i)) -> ∀ i -> isInjective (f {i})

{-
  record InjVars : 𝒰 𝑗 where
    constructor injvars
    field ⟨_⟩ : List (Jdg₂ K)
  open InjVars public

  instance
    isCategory:InjVars : isCategory (InjVars)
    isCategory.Hom isCategory:InjVars = λ a b -> injVars ⟨ a ⟩ ⟨ b ⟩
    isCategory.isSetoid:Hom isCategory:InjVars = isSetoid:byPath
    isCategory.id isCategory:InjVars = {!!}
    isCategory._◆_ isCategory:InjVars = {!!}
    isCategory.unit-l-◆ isCategory:InjVars = {!!}
    isCategory.unit-r-◆ isCategory:InjVars = {!!}
    isCategory.unit-2-◆ isCategory:InjVars = {!!}
    isCategory.assoc-l-◆ isCategory:InjVars = {!!}
    isCategory.assoc-r-◆ isCategory:InjVars = {!!}
    isCategory._◈_ isCategory:InjVars = {!!}

  ∂ₖ₃ : Jdg₂ K -> Jdg₂ K
  ∂ₖ₃ (αs ⇒ α) = αs ⇒ (∂ₖ α)
  -}


  extendctx : (Δ Γ : List (Jdg₂ K)) -> List (Jdg₂ K)
  extendctx Δ Γ = map f Δ
    where
      f : Jdg₂ K -> Jdg₂ K
      f (a ⇒ b) = Γ ⋆ a ⇒ b

  extendctx' : (Γ : List (Jdg₂ K)) -> (Δ : ⋆List (Jdg₂ K)) -> ⋆List (Jdg₂ K)
  extendctx' Γ Δ = map f Δ
    where
      f : Jdg₂ K -> Jdg₂ K
      f (a ⇒ b) = Γ ⋆ a ⇒ b

  γₗ : List (Jdg₂ K) -> (Jdg₂ K) -> Jdg₂ K
  γₗ Γ (τs ⇒ τ) = (Γ ⋆ τs ⇒ τ)

  -- γₗ! : List (Jdg₂ K) -> 𝐅𝐢𝐧𝐈𝐱 (Jdg₂ K) -> 𝐅𝐢𝐧𝐈𝐱 (Jdg₂ K) 
  -- γₗ! = {!!}

  γₗ! : List (Jdg₂ K) -> ⋆List (Jdg₂ K) -> ⋆List (Jdg₂ K)
  γₗ! Γ = map (γₗ Γ)

  γₗ* : List (Jdg₂ K) -> 𝐈𝐱 (Jdg₂ K) (𝐔𝐧𝐢𝐯 𝑖) -> 𝐈𝐱 (Jdg₂ K) (𝐔𝐧𝐢𝐯 𝑖)
  γₗ* Γ s = indexed (λ i → ix s (γₗ Γ i))



  mutual



    -- data Pat-pats (𝔍 : ⋆List (Jdg₂ K)) (Γ : List (Jdg₂ K)) (Δ : ⋆List (Jdg₂ K)) : 𝒰 (𝑖) where
    --   lam : 𝑒𝑙 Δ ⟶ indexed (λ {j -> 𝔍 ⊩ᶠ-pat (γₗ Γ j)}) -> Pat-pats 𝔍 Γ Δ

    data Pat-pats (Γ : List (Jdg₂ ⟨ K' ⟩)) : (Δ : ⋆List (Jdg₂ ⟨ K' ⟩)) (𝔍 : ⋆List (Jdg₂ ⟨ K' ⟩)) -> 𝒰 𝑖 where
      incl : ∀{𝔍 : (⋆List (Jdg₂ ⟨ K' ⟩))} -> ∀{j} -> 𝔍 ⊩ᶠ-pat (γₗ Γ j) -> Pat-pats Γ (incl j) 𝔍
      _⋆-⧜_ : ∀{j1 j2 k1 k2} -> Pat-pats Γ j1 k1 -> Pat-pats Γ j2 k2 -> Pat-pats Γ (j1 ⋆ j2) (k1 ⋆ k2)
      ◌-⧜ : Pat-pats Γ ◌ ◌


    -- this should already be η-long
    data _⊩ᶠ-pat_ : (𝔍s : ⋆List (Jdg₂ K)) -> Jdg₂ K -> 𝒰 (𝑖) where

      app-meta  : ∀{𝔍} {Γ Δ : ⟨ InjVars ⟩} {α : K}
                -> (M : 𝔍 ∍ ((⟨ ⟨ Δ ⟩ ⟩ ⇒ α))) -> (s : (Δ) ⟶ (Γ))
                -> 𝔍 ⊩ᶠ-pat (⟨ ⟨ Γ ⟩ ⟩  ⇒ α)

      app-var : ∀{𝔍 Γ Δ α}
              -> ι Γ ∍ (Δ ⇒ α) -> Pat-pats Γ (ι Δ) (𝔍)
              -- -> (∀ {i} -> ι Δ ∍ i -> 𝔍 ⊩ᶠ-patlam (Γ ∥ i))
              -> 𝔍 ⊩ᶠ-pat (Γ ⇒ α)

      app-con : ∀{𝔍 Γ Δ α}
              -> TermCon (Δ ⇒ α) -> Pat-pats Γ (ι Δ) (𝔍)
              -- -> (∀ {i} -> ι Δ ∍ i -> 𝔍 ⊩ᶠ-patlam (Γ ∥ i))
              -> 𝔍 ⊩ᶠ-pat (Γ ⇒ α)


  Pat : 𝐅𝐢𝐧𝐈𝐱 (Jdg₂ K) -> 𝐈𝐱 (Jdg₂ K) (𝐔𝐧𝐢𝐯 𝑖)
  Pat (incl js) = indexed (λ j → js ⊩ᶠ-pat j)

  refree-pats : ∀{Γ Δ X} -> 𝑒𝑙 Δ ⟶ γₗ* Γ X -> 𝑒𝑙 (γₗ! Γ Δ) ⟶ X
  refree-pats {Γ} = refree
  -- refree-𝐅𝐢𝐧𝐈𝐱 (γₗ Γ)

  cofree-pats : ∀{Γ Δ X} -> 𝑒𝑙 (γₗ! Γ Δ) ⟶ X -> 𝑒𝑙 Δ ⟶ γₗ* Γ X
  cofree-pats {Γ} = recofree
  -- recofree-𝐅𝐢𝐧𝐈𝐱 (γₗ Γ)



  mutual
    apply-injVars-lam : ∀{𝔍 Γ₀ Γ₁ Δ} -> injVars (Γ₀) (Γ₁)
                               -> Pat-pats Γ₀ Δ 𝔍 
                              -> Pat-pats Γ₁ Δ 𝔍 
    apply-injVars-lam ι = {!!} -- (lam ts) = lam λ i x → apply-injVars (ι ⇃⊗⇂ id) (ts i x)

    apply-injVars : ∀{ℑ Γ Δ α}
                              -> injVars (Δ) (Γ)
                              -> (ℑ ⊩ᶠ-pat (Δ ⇒ (α)))
                              -> (ℑ ⊩ᶠ-pat (Γ ⇒ (α)))
    apply-injVars ι (app-meta M κ) = app-meta M (κ ◆ ι)
    apply-injVars ι (app-var v ts) = app-var (⟨ ⟨ ⟨ ι ⟩ ⟩ ⟩ _ v) (apply-injVars-lam ι ts)
    apply-injVars ι (app-con c ts) = app-con c (apply-injVars-lam ι ts)

    -- apply-injVars (app-var v ts) ι = {!!} -- app-var (⟨ ⟨ ⟨ ι ⟩ ⟩ ⟩ _ v) λ x → apply-injVars-lam (ts x) ι
    -- apply-injVars (app-con c ts) ι = {!!} -- app-con c λ x → apply-injVars-lam (ts x) ι

  cancel-injective-app-var : ∀{Γ Δ Δ' α j}
              -> {x : ι Γ ∍ (Δ ⇒ α)}    -> {ts : Pat-pats Γ (ι Δ) j}   --  -> {ts : ∀ {i} -> ι Δ ∍ i -> j ⊩ᶠ-patlam (Γ ∥ i)}
              -> {x' : ι Γ ∍ (Δ' ⇒ α)}  -> {ts' : Pat-pats Γ (ι Δ') j} --  -> {ts' : ∀ {i} -> ι Δ' ∍ i -> j ⊩ᶠ-patlam (Γ ∥ i)}
              -> app-var x ts ≡ app-var x' ts' -> ∑ λ (p : Δ ≡ Δ') -> PathP (λ i -> ι Γ ∍ (p i ⇒ α)) x x'
  cancel-injective-app-var p = {!!}

  cancel-injective-app-var' : ∀{Γ Δ α j}
              -> {x : ι Γ ∍ (Δ ⇒ α)}    -> {ts : Pat-pats Γ (ι Δ) j}
              -> {x' : ι Γ ∍ (Δ ⇒ α)}  -> {ts' : Pat-pats Γ (ι Δ) j}
              -> app-var x ts ≣ app-var x' ts' -> ts ≣ ts'
  cancel-injective-app-var' p = {!!}

  cancel-injective-app-con' : ∀{Γ Δ j} {α : K}
              -> {x  : TermCon (Δ ⇒ α)}  -> {ts  : Pat-pats Γ (ι Δ) j}
              -> {x' : TermCon (Δ ⇒ α)}  -> {ts' : Pat-pats Γ (ι Δ) j}
              -> app-con x ts ≣ app-con x' ts' -> ts ≣ ts'
  cancel-injective-app-con' p = {!!}

  -- cancel-injective-lam : {𝔍 : ⋆List (Jdg₂ K)} {Γ : List (Jdg₂ K)} {Δ : ⋆List (Jdg₂ K)} 
  --                        -> {f g : 𝑒𝑙 Δ ⟶ indexed (λ {j -> 𝔍 ⊩ᶠ-pat (γₗ Γ j)})}
  --                        -> lam f ≣ lam g
  --                        -> f ∼ g
  -- cancel-injective-lam = {!!}

{-
{-

{-
{-
  -- _⊩ᶠ-pat_ : (𝔍s : List (Jdg₂ K)) -> Jdg₂ K -> 𝒰 (𝑗 ､ 𝑖)
  -- _⊩ᶠ-pat_ = _⊩ᶠ-pat_
  -- ∑ λ Γ -> ∑ λ Δ -> (Γ ⋆ Δ ∼ ℑ) × (𝔍s ⊩ᶠ-pat (Γ ∥ (Δ ⇒ α)))

{-

  -- open-η : ∀{ℑ Γ Δ α}
  --          -> (ℑ ⊩ᶠ-pat (Γ ∥ (Δ ⇒ α)))
  --          -> (ℑ ⊩ᶠ-pat ((Δ ⋆ Γ) ∥ ([] ⇒ α)))
  -- open-η {ℑ} {Γ} {⦋⦌} t = {!!}
  -- open-η {ℑ} {Γ} {x ∷ D} (lam t s) =
  --   let s' = open-η s
  --   in {!!}

  apply-injVars : ∀{ℑ Γ Δ α} -> (ℑ ⊩ᶠ-pat (Δ ∥ (α)))
                            -> injVars Γ Δ
                            -> (ℑ ⊩ᶠ-pat (Γ ∥ (α)))
  apply-injVars (app-meta M κ) ι =
    let s' = κ
    in app-meta M {!!}
  apply-injVars (app-var v ts) ι = app-var (fst ι v) λ x → apply-injVars (ts x) ι
  apply-injVars (app-con c ts) ι = app-con c λ x → apply-injVars (ts x) ι
  apply-injVars (lam ts) ι = lam (apply-injVars ts {!!})

  open-lam : ∀{ℑ Δ₁ Δ₂ Δ α} -> (Δ₁ ⋆ Δ₂ ∼ Δ) -> (ℑ ⊩ᶠ-pat (Δ₁ ∥ (Δ₂ ⇒ α)))
             -> (ℑ ⊩ᶠ-pat (Δ ∥ ([] ⇒ α)))
  open-lam {ℑ} {Δ₁ = Δ₁} {Δ₂ = ⦋⦌} {Δ} {α} refl-≣ t =
    transport-Str (cong-Str p (unit-r-⋆ {a = Δ₁} ⁻¹)) t
      where p = (λ ξ -> ℑ ⊩ᶠ-pat (ξ ∥ ([] ⇒ α)))
  open-lam {Δ₂ = x ∷ Δ₂} refl-≣ (lam t) = t

  open-injVars : ∀{ℑ Γ Δ₁ Δ₂ Δ α} -> (Δ₁ ⋆ Δ₂ ∼ Δ) -> (ℑ ⊩ᶠ-pat (Δ₁ ∥ (Δ₂ ⇒ α)))
                            -> injVars Γ Δ
                            -> (ℑ ⊩ᶠ-pat (Γ ∥ ([] ⇒ α)))
  open-injVars {Δ₂ = ⦋⦌} refl-≣ t s = apply-injVars t (s ◆ {!!})
  -- apply-injVars t s
  open-injVars {Δ₂ = x ∷ Δ₂} refl-≣ (lam t) s = apply-injVars t s
  -- open-injVars {Δ₂ = ⦋⦌} t ι = apply-injVars t ι
  -- open-injVars {Δ₂ = x ∷ Δ} (lam t) ι = apply-injVars t ι

  -- open-injVars : ∀{ℑ Γ Δ α} -> (ℑ ⊩ᶠ-pat ([] ∥ (Δ ⇒ α)))
  --                           -> injVars Γ Δ
  --                           -> (ℑ ⊩ᶠ-pat (Γ ∥ ([] ⇒ α)))
  -- open-injVars {Δ = ⦋⦌} t ι = apply-injVars t ι
  -- open-injVars {Δ = x ∷ Δ} (lam t) ι = apply-injVars t ι

  _⊩ᶠ-pat_ : (𝔍s : List (Jdg₂ K)) -> Jdg₂ K -> 𝒰 (𝑗 ､ 𝑖)
  _⊩ᶠ-pat_ 𝔍s (ℑ ⇒ α) = ∑ λ Γ -> ∑ λ Δ -> (Γ ⋆ Δ ∼ ℑ) × (𝔍s ⊩ᶠ-pat (Γ ∥ (Δ ⇒ α)))


-}

-}
-}
-}

-}
