
{-# OPTIONS --experimental-lossy-unification #-}
module Verification.Core.Theory.Std.Specific.FirstOrderTerm.Instance.hasEpiMonoFactorization where

open import Verification.Conventions hiding (_⊔_)

open import Verification.Core.Set.Contradiction
open import Verification.Core.Set.Discrete
open import Verification.Core.Set.Decidable
open import Verification.Core.Algebra.Monoid.Definition
open import Verification.Core.Algebra.Monoid.Free
open import Verification.Core.Data.List.Variant.Binary.Instance.Monoid
open import Verification.Core.Data.List.Variant.Binary.Element.Definition
open import Verification.Core.Data.Universe.Definition
open import Verification.Core.Data.Universe.Instance.Category
open import Verification.Core.Data.Universe.Instance.FiniteCoproductCategory
open import Verification.Core.Data.Product.Definition
open import Verification.Core.Data.Sum.Definition
open import Verification.Core.Data.List.Variant.Unary.Definition

open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Category.Std.Category.Discrete
open import Verification.Core.Category.Std.Category.Structured.Monoidal.Definition
open import Verification.Core.Category.Std.Functor.Definition
open import Verification.Core.Category.Std.RelativeMonad.Definition
open import Verification.Core.Category.Std.RelativeMonad.KleisliCategory.Definition
open import Verification.Core.Category.Std.RelativeMonad.KleisliCategory.Instance.FiniteCoproductGenerated
open import Verification.Core.Category.Std.Category.Subcategory.Definition
open import Verification.Core.Category.Std.Morphism.EpiMono
open import Verification.Core.Category.Std.Morphism.Iso
open import Verification.Core.Category.Std.Limit.Specific.Coproduct.Definition
open import Verification.Core.Category.Std.Functor.Adjoint

-- for coproducts of ⧜𝐒𝐮𝐛𝐬𝐭
-- open import Verification.Core.Category.Std.Limit.Specific.Coproduct.Reflection.Definition

-- open import Verification.Core.Data.Indexed.Duplicate

open import Verification.Core.Data.List.Variant.Binary.Natural
open import Verification.Core.Data.Indexed.Definition
open import Verification.Core.Data.Indexed.Instance.Monoid
open import Verification.Core.Data.Indexed.Instance.FiniteCoproductCategory
open import Verification.Core.Data.FiniteIndexed.Definition
open import Verification.Core.Data.FiniteIndexed.Instance.FiniteCoproductGenerated
open import Verification.Core.Data.Renaming.Definition
open import Verification.Core.Data.Renaming.Instance.CoproductMonoidal
open import Verification.Core.Data.Substitution.Variant.Base.Definition
open import Verification.Core.Data.List.Dependent.Variant.Binary.Definition
open import Verification.Core.Data.List.Variant.Binary.Element.Definition
open import Verification.Core.Data.List.Variant.Binary.ElementSum.Definition
open import Verification.Core.Data.List.Variant.Binary.ElementSum.Instance.Category

open import Verification.Core.Theory.Std.Generic.FormalSystem.Definition
open import Verification.Core.Theory.Std.Specific.FirstOrderTerm.Definition
open import Verification.Core.Theory.Std.Specific.FirstOrderTerm.Signature
open import Verification.Core.Theory.Std.Specific.FirstOrderTerm.Substitution.Definition
open import Verification.Core.Theory.Std.Specific.FirstOrderTerm.Instance.RelativeMonad
-- open import Verification.Core.Theory.Std.Specific.FirstOrderTerm.Instance.FormalSystem
open import Verification.Core.Theory.Std.Specific.FirstOrderTerm.Element
open import Verification.Core.Theory.Std.Specific.FirstOrderTerm.Unification.PCF.Occur

open import Verification.Core.Category.Std.Factorization.EpiMono.Variant.Split.Definition
open import Verification.Core.Category.Std.Category.Structured.FiniteCoproductGenerated

record hasMembership {𝑘} {𝑖} {𝑗} (A : 𝒰 𝑖) (B : 𝒰 𝑗) : 𝒰 (𝑖 ､ 𝑗 ､ 𝑘 ⁺) where
  constructor hasMembership:byDef
  field _∋_ : A -> B -> 𝒰 𝑘

open hasMembership {{...}} public

instance
  hasMembership:⋆List : ∀{A : 𝒰 𝑖} -> hasMembership (⋆List A) A
  hasMembership:⋆List = hasMembership:byDef (λ as a → as ∍ a)

-- instance
--   hasMembership:List : ∀{A : 𝒰 𝑖} -> hasMembership (List A) A
--   hasMembership:List = hasMembership:byDef (λ as a → as ♮∍ a)



module _ {Σ : 𝒯FOSignature 𝑖} where
  instance
    hasMembership:𝐂𝐭𝐱 : hasMembership (⧜𝐒𝐮𝐛𝐬𝐭 (𝒯⊔term Σ)) _
    hasMembership:𝐂𝐭𝐱 = hasMembership:byDef (λ a i → ⟨ a ⟩ ∍ i)

  instance
    hasMembership:𝒯⊔Term : ∀{a i j} -> hasMembership (𝒯⊔Term Σ a i) (a ∍ j)
    hasMembership:𝒯⊔Term = hasMembership:byDef (λ t p → VarPath-Term-𝕋× Σ t p)

  instance
    hasMembership:𝒯⊔Terms : ∀{a b j} -> hasMembership (𝒯⊔Terms Σ a b) (b ∍ j)
    hasMembership:𝒯⊔Terms = hasMembership:byDef (λ t p → VarPath-𝒯⊔Terms Σ t p)


  private
    module _ {a : ⧜𝐒𝐮𝐛𝐬𝐭 (𝒯⊔term Σ)} {s} where
      asArr : 𝒯⊔Term Σ ⟨ a ⟩ s -> incl (incl s) ⟶ a
      asArr t = ⧜subst (incl t)

  module _ {a b : ⧜𝐒𝐮𝐛𝐬𝐭 (𝒯⊔term Σ)} {f g : a ⟶ b} where
    lem-001 : (∀{i} (a∍i : ⟨ a ⟩ ∍ i) -> asArr (var a∍i) ◆ f ∼ asArr (var a∍i) ◆ g) -> f ∼ g
    lem-001 = {!!}

  -- first, a map/substitution is epi if all variables in the target are somewhere in the terms
  -- of the substitution
  module _ {a b : ⧜𝐒𝐮𝐛𝐬𝐭 (𝒯⊔term Σ)} where
    isEpi-𝕋× : (f : a ⟶ b) -> 𝒰 _
    isEpi-𝕋× f = ∀{i} -> (p : ⟨ b ⟩ ∍ i) -> ∑ λ j -> ∑ λ (q : ⟨ a ⟩ ∍ j) -> (destruct-⋆Listᴰ ⟨ f ⟩ j q) ∋ p

  private
    module _ {a b : ⧜𝐒𝐮𝐛𝐬𝐭 (𝒯⊔term Σ)} where
      mutual
        lem-01s : ∀{x} (t : CtxHom (𝒯⊔Term Σ) x ⟨ a ⟩) (g h : a ⟶ b) -> ((⧜subst t) ◆ g ∼ (⧜subst t) ◆ h) -> ∀{i} (ip : ⟨ a ⟩ ∍ i) -> VarPath-𝒯⊔Terms Σ t ip -> asArr (var ip) ◆ g ∼ asArr (var ip) ◆ h
        lem-01s (incl x) g h tg∼th ip (incl p) = lem-01 x g h tg∼th ip p
        lem-01s (t ⋆-⧜ s) g h tg∼th ip (left-Path pat) = lem-01s t g h {!!} ip pat
        lem-01s (t ⋆-⧜ s) g h tg∼th ip (right-Path pat) = lem-01s s g h {!!} ip pat

        lem-01 : ∀{s} (t : 𝒯⊔Term Σ ⟨ a ⟩ s) (g h : a ⟶ b) -> (asArr t ◆ g ∼ asArr t ◆ h) -> ∀{i} (ip : ⟨ a ⟩ ∍ i) -> VarPath-Term-𝕋× Σ t ip -> asArr (var ip) ◆ g ∼ asArr (var ip) ◆ h
        lem-01 (var x) g h tg∼th .x (var .x) = tg∼th
        lem-01 (con c x) g h tg∼th ip (con .c x₁) =
          let
              lem-01a : ((asArr (con c x) ◆-⧜𝐒𝐮𝐛𝐬𝐭 g)) ∼ (asArr (con c x) ◆-⧜𝐒𝐮𝐛𝐬𝐭 h)
              lem-01a = {!!}
              lem-01b : ((⧜subst x ◆-⧜𝐒𝐮𝐛𝐬𝐭 g)) ∼ (⧜subst x ◆-⧜𝐒𝐮𝐛𝐬𝐭 h)
              lem-01b = {!!}
              lem-01c : ((⧜subst x ◆ g)) ∼ (⧜subst x ◆ h)
              lem-01c = {!!}
          in lem-01s x g h lem-01c ip x₁

    module _ {a b : ⧜𝐒𝐮𝐛𝐬𝐭 (𝒯⊔term Σ)} where
      module _ {f : a ⟶ b} (P : isEpi-𝕋× f) {x : ⧜𝐒𝐮𝐛𝐬𝐭 (𝒯⊔term Σ)} {g h : b ⟶ x} (fg∼fh : f ◆ g ∼ f ◆ h) where
        lem-20 : g ∼ h
        lem-20 = lem-001 λ a∍i →
                 let j , q , pat = P a∍i
                 in lem-01 ((destruct-⋆Listᴰ ⟨ f ⟩ j q)) g h {!!} a∍i pat


      prop-1 : {f : a ⟶ b} -> isEpi-𝕋× f -> isEpi f
      prop-1 P = epi (lem-20 P)

    -- we can remove unused metavariables
    abstract

      mutual
        prop-3s : ∀{a bₐ bₓ : ⧜𝐒𝐮𝐛𝐬𝐭 (𝒯⊔term Σ)} (f : CtxHom (𝒯⊔Term Σ) ⟨ a ⟩ (⟨ bₐ ⟩ ⋆ ⟨ bₓ ⟩))
                  -> (∀{i} -> (bₓ∍i : ⟨ bₓ ⟩ ∍ i) -> ¬ (VarPath-𝒯⊔Terms Σ f (right-∍ bₓ∍i)))
                  -> ∑ λ (f' : a ⟶ bₐ) -> f' ◆ ι₀ ∼ ⧜subst f
        prop-3s ◌-⧜ ¬right = (elim-⊥) , expand-⊥ ∙ expand-⊥ ⁻¹
        prop-3s (incl x) ¬right = let x' , xp = prop-3 x λ bₓ∍i x₁ → ¬right bₓ∍i (incl x₁) in ⧜subst (incl x') , xp
        prop-3s (f ⋆-⧜ g) ¬right =
          let f' , f'p = prop-3s f λ bₓ∍i x → ¬right bₓ∍i (left-Path x)
              g' , g'p = prop-3s g λ bₓ∍i x → ¬right bₓ∍i (right-Path x)
              lem-1 : f' ◆ ι₀ ∼ ⧜subst f
              lem-1 = f'p

              lem-2 : g' ◆ ι₀ ∼ ⧜subst g
              lem-2 = g'p

              lem-3 : ⦗ f' , g' ⦘ ◆ ι₀ ∼ ⦗ ⧜subst f , ⧜subst g ⦘
              lem-3 = append-⦗⦘ ∙ ⦗≀ lem-1 , lem-2 ≀⦘

              lem-4 : ⦗ ⧜subst f , ⧜subst g ⦘ ∼ ⧜subst (f ⋆-⧜ g)
              lem-4 = {!!}

          in ⦗ f' , g' ⦘ , lem-3 ∙ lem-4


        prop-3 : ∀{bₐ bₓ : ⧜𝐒𝐮𝐛𝐬𝐭 (𝒯⊔term Σ)} {a} (f : 𝒯⊔Term Σ (⟨ bₐ ⟩ ⋆ ⟨ bₓ ⟩) a)
                -> (∀{i} -> (bₓ∍i : ⟨ bₓ ⟩ ∍ i) -> ¬ (f ∋ right-∍ bₓ∍i))
                -> ∑ λ (f' : 𝒯⊔Term Σ ⟨ bₐ ⟩ a) -> (asArr f') ◆ ι₀ ∼ asArr f
        prop-3 (var (right-∍ x)) ¬right = impossible (¬right x (var (right-∍ x)))
        prop-3 (var (left-∍ x)) ¬right = (var x) , abstract-◆-⧜𝐒𝐮𝐛𝐬𝐭 ⁻¹ ∙ cong-Str ⧜subst (cong-Str incl {!!}) -- lem-1
          -- where
          --   lem-1 : (asArr (var x) ◆-⧜𝐒𝐮𝐛𝐬𝐭 ι₀) ∼ asArr (var (left-∍ x))
          --   lem-1 = {!!}

        prop-3 (con c x) ¬right =
          let f , fp = prop-3s x λ bₓ∍i x₁ → ¬right bₓ∍i (con c x₁)
          in (con c ⟨ f ⟩) , {!!}

    optimize-metas = prop-3s

    module _ {a b : ⧜𝐒𝐮𝐛𝐬𝐭 (𝒯⊔term Σ)} {f : a ⟶ b} where

      private
        bs = fcgSize b
        b'ᵘ : [ bs ]ᶠ -> ⧜𝐒𝐮𝐛𝐬𝐭 (𝒯⊔term Σ)
        b'ᵘ = ⟨ fcg b ⟩
        macro b' = #structureOn b'ᵘ

        -- abstract
        --   β : (v : [ bs ]ᶠ) -> isDecidable (⟨ f ⟩ ∋ b' v)
        --   β (member v) = isFreeVars ⟨ f ⟩ v

        {-
        b₀f : [ ⟨ b ⟩ ]ᶠ -> ⧜𝐒𝐮𝐛𝐬𝐭 (𝒯⊔term Σ)
        b₀f x with β x
        ... | (left _) = incl (incl (getMemberSort x))
        ... | (right _) = ⊥

        b₁f : [ ⟨ b ⟩ ]ᶠ -> ⧜𝐒𝐮𝐛𝐬𝐭 (𝒯⊔term Σ)
        b₁f x with β x
        ... | (left _) = ⊥
        ... | (right _) = incl (incl (getMemberSort x))

        ιbf : (v : [ ⟨ b ⟩ ]ᶠ) -> incl (incl (getMemberSort v)) ⟶ b₀f v ⊔ b₁f v
        ιbf v with β v
        ... | left x = ι₀
        ... | just x = ι₁

        ιb₀f : (v : [ ⟨ b ⟩ ]ᶠ) -> b₀f v ⟶ incl (incl (getMemberSort v))
        ιb₀f v with β v
        ... | left x = id
        ... | just x = elim-⊥

        ιb₁f : (v : [ ⟨ b ⟩ ]ᶠ) -> b₁f v ⟶ incl (incl (getMemberSort v))
        ιb₁f v with β v
        ... | left x = elim-⊥
        ... | just x = id

        b₀ : ⧜𝐒𝐮𝐛𝐬𝐭 (𝒯⊔term Σ)
        b₀ = ⨆ᶠ {!b₀f since isFunctor:byDiscrete!} -- (indexed b₀f)

        b₁ : ⧜𝐒𝐮𝐛𝐬𝐭 (𝒯⊔term Σ)
        b₁ = ⨆ᶠ {!!} -- (indexed b₁f)

        bF : 𝐈𝐱 [ ⟨ b ⟩ ]ᶠ (⧜𝐒𝐮𝐛𝐬𝐭 (𝒯⊔term Σ))
        bF = indexed (λ (x : [ ⟨ b ⟩ ]ᶠ) → incl (incl (getMemberSort x)))
        -}

      {-
        {-
        ϕ : (⨆ᶠ bF) ⟶ (b₀ ⊔ b₁)
        ϕ = ⦗ ϕ' ⦘ᶠ
          where
            ϕ' : bF ⟶ 写 (b₀ ⊔ b₁)
            ϕ' i = ιbf i ◆ ⦗ ιᶠ i ◆ ι₀ , ιᶠ i ◆ ι₁ ⦘

        ϕ⁻¹ : b₀ ⊔ b₁ ⟶ ⨆ᶠ bF
        ϕ⁻¹ = ⦗ map-⨆ᶠ ιb₀f , map-⨆ᶠ ιb₁f ⦘

        ϕ' : (⨆ᶠ bF) ≅ (b₀ ⊔ b₁)
        ϕ' = ϕ since record { inverse-◆ = ϕ⁻¹ ; inv-r-◆ = {!!} ; inv-l-◆ = {!!} }

        ρ₀ : b ⟶ ⨆ᶠ bF
        ρ₀ = surj-map-ι-⧜𝐒𝐮𝐛𝐬𝐭 (incl (lem-1 {b = ⟨ b ⟩}))
          where
            lem-1 : ∀{b} -> (i : Sort Σ) → b ∍ i → 𝒯⊔Term Σ ⟨ ⨆ᶠᵘ (indexed (λ (x : [ b ]ᶠ) → incl (incl (fst x)))) ⟩ i
            lem-1 {incl x₁} i x = var x
            lem-1 {b ⋆-⧜ b₂} i (right-∍ x) = {!!}
            lem-1 {b ⋆-⧜ b₂} i (left-∍ x) = {!!}

        ρ : b ≅ ⨆ᶠ bF
        ρ = ρ₀ since {!!}

        f' : a ⟶ b₀ ⊔ b₁
        f' = f ◆ ⟨ (ρ ∙-≅ ϕ') ⟩

        f'e : a ⟶ b₀
        f'e = optimize-metas ⟨ f' ⟩ {!!} .fst
        -}


      factorize-𝕋× : isSplitEpiMonoFactorizable f
      image factorize-𝕋× = b₀
      rest factorize-𝕋× = b₁
      splitting factorize-𝕋× = ? -- sym-≅ (ρ ∙-≅ ϕ')
      epiHom factorize-𝕋× = ? -- f'e
      isEpi:epiHom factorize-𝕋× = {!!}
      factors factorize-𝕋× = {!!}



  -- finally, this means that ⧜𝐒𝐮𝐛𝐬𝐭 (𝒯⊔term Σ) has epi mono factorization
  instance
    hasSplitEpiMonoFactorization:𝐂𝐭𝐱-𝕋× : hasSplitEpiMonoFactorization (⧜𝐒𝐮𝐛𝐬𝐭 (𝒯⊔term Σ))
    hasSplitEpiMonoFactorization:𝐂𝐭𝐱-𝕋× = record { factorize = λ _ -> factorize-𝕋× }

-}





