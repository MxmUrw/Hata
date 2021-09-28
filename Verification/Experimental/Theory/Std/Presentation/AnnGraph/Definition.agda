
module Verification.Experimental.Theory.Std.Presentation.AnnGraph.Definition where


open import Verification.Conventions
open import Verification.Experimental.Set.Function.Surjective
open import Verification.Experimental.Algebra.Monoid.Definition
open import Verification.Experimental.Data.Product.Definition
open import Verification.Experimental.Data.Sum.Definition
open import Verification.Experimental.Data.Sum.Instance.Functor
open import Verification.Experimental.Data.Universe.Everything
open import Verification.Experimental.Category.Std.Category.Definition
open import Verification.Experimental.Category.Std.Functor.Definition


module _ {ℬ : Category 𝑖} (F : Functor ℬ (𝐔𝐧𝐢𝐯 𝑗)) where
  record isAnnGraph (E : 𝒰 𝑘) (V : 𝒰 𝑘) : 𝒰 (𝑖 ､ 𝑗 ､ 𝑘) where
    constructor anngraph
    field bo : V -> ⟨ ℬ ⟩
    field source : E -> ∑ λ v -> ⟨ F ⟩ (bo v)
    field target : E -> ∑ λ v -> ⟨ F ⟩ (bo v)

  open isAnnGraph {{...}} public

  AnnGraph : (E : 𝒰 𝑘) -> _
  AnnGraph E = _ :& isAnnGraph E


module _ {ℬ : Category 𝑖} {F : Functor ℬ (𝐔𝐧𝐢𝐯 𝑗)} where

  module _ {E : 𝒰 𝑘} where

    data UPath (𝒜 : AnnGraph F E) : (a b : ⟨ 𝒜 ⟩) -> 𝒰 (𝑖 ､ 𝑗 ､ 𝑘) where
      [] : ∀{a} -> UPath 𝒜 a a
      step₊ : ∀{a b c} -> (e : E) -> source e .fst ≡ a -> target e .fst ≡ b -> UPath 𝒜 b c -> UPath 𝒜 a c
      step₋ : ∀{a b c} -> (e : E) -> target e .fst ≡ a -> source e .fst ≡ b -> UPath 𝒜 b c -> UPath 𝒜 a c

    trans-UPath : ∀{𝒜 : AnnGraph F E} {a b c : ⟨ 𝒜 ⟩} -> (UPath 𝒜 a b) -> UPath 𝒜 b c -> UPath 𝒜 a c
    trans-UPath = {!!}

    sym-UPath : ∀{𝒜 : AnnGraph F E} {a b : ⟨ 𝒜 ⟩} -> (UPath 𝒜 a b) -> UPath 𝒜 b a
    sym-UPath [] = []
    sym-UPath (step₊ e x x₁ p) = {!!} -- step₋ e {!!} {!!} {!!}
    sym-UPath (step₋ e x x₁ p) = {!!}

    isConnected : AnnGraph F E -> 𝒰 _
    isConnected 𝒜 = ∀(a b : ⟨ 𝒜 ⟩) -> UPath 𝒜 a b

    isContracted : AnnGraph F E -> 𝒰 _
    isContracted 𝒜 = ∀(e : E) -> source e ≡ target e

    module _ (𝒜 ℬ : AnnGraph F E) where
      record isAnnHom (f : ⟨ 𝒜 ⟩ -> ⟨ ℬ ⟩) : 𝒰 (𝑖 ､ 𝑗 ､ 𝑘) where
        field mapBo : ∀{v : ⟨ 𝒜 ⟩} -> bo v ⟶ bo (f v)
        field compatSource : ∀{e : E} -> source e ≡ (f (fst (source e)) , map mapBo (snd (source e)))
        field compatTarget : ∀{e : E} -> target e ≡ (f (fst (target e)) , map mapBo (snd (target e)))

      AnnHom = _ :& isAnnHom

      open isAnnHom {{...}} public


    module §-AnnGraph where
      prop-2 : ∀{𝒜 ℬ : AnnGraph F E} -> (h : AnnHom 𝒜 ℬ) -> ∀{a b : ⟨ 𝒜 ⟩} -> (p : UPath 𝒜 a b) -> UPath ℬ (⟨ h ⟩ a) (⟨ h ⟩ b)
      prop-2 h {a} {.a} [] = []
      prop-2 h {a} {b} (step₊ e p1 p2 r) = step₊ e
                                                 (trans-Path (cong fst compatSource) (cong ⟨ h ⟩ p1))
                                                 (trans-Path (cong fst compatTarget) (cong ⟨ h ⟩ p2))
                                                 (prop-2 h r)

      prop-2 h {a} {b} (step₋ e p1 p2 r) = step₋ e
                                                 (trans-Path (cong fst compatTarget) (cong ⟨ h ⟩ p1))
                                                 (trans-Path (cong fst compatSource) (cong ⟨ h ⟩ p2))
                                                 (prop-2 h r)

      prop-1 : ∀{𝒜 ℬ : AnnGraph F E} -> (h : AnnHom 𝒜 ℬ) -> {{_ : isSurjective-𝒰 ⟨ h ⟩}} -> isConnected 𝒜 -> isConnected ℬ
      prop-1 {𝒜} {ℬ} h 𝒜p a b = p3
        where
          p0 : UPath 𝒜 (surj-𝒰 a) (surj-𝒰 b)
          p0 = 𝒜p _ _

          p1 : UPath ℬ (⟨ h ⟩ (surj-𝒰 a)) (⟨ h ⟩ (surj-𝒰 b))
          p1 = prop-2 h p0

          pair' : ⟨ ℬ ⟩ ×-𝒰 ⟨ ℬ ⟩
          pair' = a , b

          q : (⟨ h ⟩ (surj-𝒰 a) , ⟨ h ⟩ (surj-𝒰 b)) ≡ pair'
          q = cong₂ _,_ inv-surj-𝒰 inv-surj-𝒰

          p3 : UPath ℬ a b
          p3 = transport (λ i -> UPath ℬ (q i .fst) (q i .snd)) p1

      private
        infixl 40 _∙:_
        _∙:_ = trans-Path

      prop-4 : ∀{𝒜 : AnnGraph F E} -> isContracted 𝒜 -> ∀(a b : ⟨ 𝒜 ⟩) -> UPath 𝒜 a b -> a ≡ b
      prop-4 contr a .a [] = refl-≡
      prop-4 contr a b (step₊ e p1 p2 r) = sym-Path p1 ∙: (cong fst (contr e)) ∙: p2 ∙: prop-4 contr _ _ r
      prop-4 contr a b (step₋ e p1 p2 r) = sym-Path p1 ∙: sym-Path (cong fst (contr e)) ∙: p2 ∙: prop-4 contr _ _ r

      prop-3 : ∀{𝒜 : AnnGraph F E} -> isConnected 𝒜 -> isContracted 𝒜 -> ∀(a b : ⟨ 𝒜 ⟩) -> a ≡ b
      prop-3 con contr a b = prop-4 contr a b (con a b)




