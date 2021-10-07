
module Verification.Experimental.Theory.Std.Specific.ProductTheory.Instance.FromANVecTree where

open import Verification.Conventions hiding (_⊔_ ; lookup)
open import Verification.Experimental.Set.Discrete
open import Verification.Experimental.Set.Contradiction
open import Verification.Experimental.Set.Setoid.Definition
open import Verification.Experimental.Set.Function.Surjective
open import Verification.Experimental.Data.Nat.Free
open import Verification.Experimental.Data.Sum.Definition
open import Verification.Experimental.Data.Product.Definition
open import Verification.Experimental.Data.Sum.Instance.Functor
open import Verification.Experimental.Category.Std.Monad.Definition
open import Verification.Experimental.Category.Std.Monad.KleisliCategory.Instance.Monoidal
open import Verification.Experimental.Category.Std.Monad.TypeMonadNotation
open import Verification.Experimental.Data.Sum.Instance.Monad
open import Verification.Experimental.Data.Universe.Everything
open import Verification.Experimental.Theory.Std.Specific.ProductTheory.Definition
open import Verification.Experimental.Theory.Std.Presentation.Token.Definition
open import Verification.Experimental.Category.Std.Category.Definition
open import Verification.Experimental.Category.Std.Functor.Definition
open import Verification.Experimental.Category.Std.Category.Subcategory.Definition
open import Verification.Experimental.Category.Std.Category.Subcategory.Full
open import Verification.Experimental.Data.Indexed.Definition
open import Verification.Experimental.Data.Indexed.Instance.Monoid
open import Verification.Experimental.Data.FiniteIndexed.Definition
open import Verification.Experimental.Algebra.Monoid.Definition
open import Verification.Experimental.Algebra.Monoid.Free
open import Verification.Experimental.Algebra.Monoid.Free.Element
open import Verification.Experimental.Data.Substitution.Definition
open import Verification.Experimental.Data.Substitution.Property.Base
open import Verification.Experimental.Theory.Std.Presentation.NGraph.Definition
open import Verification.Experimental.Category.Std.Limit.Specific.Coproduct.Definition
open import Verification.Experimental.Category.Std.Morphism.Iso

open import Verification.Experimental.Category.Std.RelativeMonad.Definition
open import Verification.Experimental.Category.Std.RelativeMonad.KleisliCategory.Definition


-- open import Verification.Experimental.Theory.Std.Specific.ProductTheory.Instance.FromString2
open import Verification.Experimental.Theory.Std.Presentation.CheckTree.Definition2
open import Verification.Experimental.Theory.Std.Specific.ProductTheory.Instance.hasBoundaries



-----------------------------------------
-- product theory specific


module _ (𝒯 : ProductTheory ℓ₀) {{_ : IShow (Sort 𝒯)}} where

  module _ {n : 人ℕ} where
    _⊫_ : ∀{b : ℬ× 𝒯} -> (Γ : CtxHom (λ b _ -> SortTermᵈ 𝒯 b) n ⟨ b ⟩) -> SortTermᵈ 𝒯 ⟨ b ⟩ -> ⟨ F× 𝒯 n ⟩ b
    _⊫_ {b} Γ τ = ⧜subst (Γ ⋆-⧜ (incl τ))

    module _ {b : ℬ× 𝒯} where
      data isSameCtx : (Γ : CtxHom (λ b _ -> SortTermᵈ 𝒯 b) n ⟨ b ⟩)
                       -> (τs : List (Sort 𝒯))
                       -> (vs : Vec (⟨ F× 𝒯 n ⟩ b) (length τs))
                       -> 𝒰 ℓ₀ where
        [] : ∀{Γ} -> isSameCtx Γ [] []
        _∷_ : ∀{Γ τs vs} -> (τ : Sort 𝒯) -> isSameCtx Γ τs vs -> isSameCtx Γ (τ ∷ τs) (Γ ⊫ con τ ∷ vs)

    data isWellTyped× {b : ℬ× 𝒯} : (a : Node 𝒯 n)
                                 -> (v : ⟨ F× 𝒯 n ⟩ b)
                                 -> (vs : Vec (⟨ F× 𝒯 n ⟩ b) (size× 𝒯 a))
                                 -> 𝒰 ℓ₀ where
      varType : (i : [ n ]ᶠ)
                -> ∀{Γ τ}
                -> atList Γ i ≣ τ
                -> isWellTyped× (isVar i) (Γ ⊫ τ) []

      conType : ∀{τs τ} -> (c : Con 𝒯 τs τ)
                -> ∀{Γ vs}
                -> isSameCtx Γ τs vs
                -> isWellTyped× (isNode (_ , _ , c)) (Γ ⊫ (con τ)) vs

-----------------------------------------
-- generic

data DVec {A : 𝒰 𝑖} (F : A -> 𝒰 𝑗) : {n : ℕ} -> (Vec A n) -> 𝒰 (𝑖 ､ 𝑗) where
  [] : DVec F []
  _∷_ : ∀{n} {a : A} {as : Vec A n} -> (x : F a) -> DVec F as -> DVec F (a ∷ as)

-- module _ (A : 𝒰 𝑖) (l : A -> ℕ) where
--   data VecTree1 : 𝒰 (𝑖) where
--     node1 : (a : A) -> (Vec VecTree1 (l a)) -> VecTree1

module _ (A : 𝒰 𝑖) (l : A -> ℕ) (ℬ : 𝒰 𝑖) {{_ : isCategory {𝑗} ℬ}} {{_ : isSet-Str ℬ}} (F : Functor ′ ℬ ′ (𝐔𝐧𝐢𝐯 𝑙)) where

  module _ (WT : ∀{b} -> (a : A) -> ⟨ F ⟩ b -> Vec (⟨ F ⟩ b) (l a) -> 𝒰 𝑘) where

    data ANVecTree (b : ℬ) : (⟨ F ⟩ b) -> 𝒰 (𝑖 ､ 𝑗 ､ 𝑙 ､ 𝑘) where
      node1 : (a : A) -> (v : ⟨ F ⟩ b) -> (vs : Vec (⟨ F ⟩ b) (l a))
              -> WT a v vs
              -> (DVec (ANVecTree b) vs) -> ANVecTree b v

    data DANVecTree : 𝒰 (𝑖 ､ 𝑗 ､ 𝑙 ､ 𝑘) where
      node1 : ∀(b : ℬ) -> (a : A) -> (v : ⟨ F ⟩ b) -> (vs : Vec (⟨ F ⟩ b) (l a))
              -> WT a v vs
              -> (Vec DANVecTree (l a)) -> DANVecTree

    data DANVecTree2 (b : ℬ) : (⟨ F ⟩ b) -> 𝒰 (𝑖 ､ 𝑗 ､ 𝑙 ､ 𝑘) where
      node1 : ∀(a : A) -> (v : ⟨ F ⟩ b) -> (vs ws : Vec (⟨ F ⟩ b) (l a))
              -> (vs ≡ ws)
              -> WT a v vs
              -> (DVec (DANVecTree2 b) ws) -> DANVecTree2 b v

    elimD2Tree : ∀{b : ℬ} -> (v : ⟨ F ⟩ b) -> DANVecTree2 b v -> ANVecTree b v
    elimD2Tree v (node1 a .v vs ws x x₁ x₂) = {!!}

    -- paths
    data DANTreeStep : (t s : DANVecTree) -> 𝒰 (𝑖 ､ 𝑗 ､ 𝑙 ､ 𝑘) where
      incl : ∀(b : ℬ) -> (a : A) -> (v : ⟨ F ⟩ b) -> (vs : Vec (⟨ F ⟩ b) (l a))
              -> (wt : WT a v vs)
              -> (ts : Vec DANVecTree (l a))
              -> (i : Fin-R (l a))
              -> DANTreeStep (lookup i ts) (node1 b a v vs wt ts)

      -- incl : ∀{a : A} -> (ts : ([ l a ]ᶠ -> (VecTree1 A l))) -> (i : [ l a ]ᶠ)
      --       -> TreeStep1 (node1 a ts) (ts i)

    data DANTreePath : (t s : DANVecTree) -> 𝒰 (𝑖 ､ 𝑗 ､ 𝑙 ､ 𝑘) where
      [] : ∀{t : DANVecTree} -> DANTreePath t t
      step : ∀{r s t : (DANVecTree)} -> DANTreePath r s -> DANTreeStep s t -> DANTreePath r t

    DANVertex : (r : DANVecTree) -> 𝒰 _
    DANVertex r = ∑ DANTreePath r

    -----------------------------------------
    -- ADAN version

    data ADANVecTree : (v : ∑ λ b -> ⟨ F ⟩ b) -> 𝒰 (𝑖 ､ 𝑗 ､ 𝑙 ､ 𝑘) where
      node1 : (a : A) -> ∀(b : ℬ) -> (v : ⟨ F ⟩ b) -> (vs : Vec (⟨ F ⟩ b) (l a))
              -> WT a v vs
              -> (Vec (∑ ADANVecTree) (l a)) -> ADANVecTree (b , v)

    data ADANTreeStep : (t s : ∑ ADANVecTree) -> (vout : ⟨ F ⟩ (t .fst .fst))  -> 𝒰 (𝑖 ､ 𝑗 ､ 𝑙 ､ 𝑘) where
      incl : (a : A) -> ∀(b : ℬ) -> (v : ⟨ F ⟩ b) -> (vs : Vec (⟨ F ⟩ b) (l a))
              -> (wt : WT a v vs)
              -> (ts : Vec (∑ ADANVecTree) (l a))
              -> (i : Fin-R (l a))
              -> ADANTreeStep (_ , node1 a b v vs wt ts) (lookup i ts) (lookup i vs)

    data ADANTreePath : (t s : ∑ ADANVecTree) -> 𝒰 (𝑖 ､ 𝑗 ､ 𝑙 ､ 𝑘) where
      [] : ∀{t : ∑ ADANVecTree} -> ADANTreePath t t
      step : ∀{r s t : (∑ ADANVecTree)} -> ∀{vout} -> ADANTreePath r s -> ADANTreeStep s t vout -> ADANTreePath r t

    ADANVertex : ∀{b} -> (v : ⟨ F ⟩ b) -> (r : ∑ ADANVecTree) -> 𝒰 _
    ADANVertex v r = ∑ λ t -> ADANTreePath r ((_ , v) , t)

    ADANEdge : ∀{b1 b2} -> (v1 : ⟨ F ⟩ b1) (v2 : ⟨ F ⟩ b2) (vout : ⟨ F ⟩ b1) -> (r : ∑ ADANVecTree) -> 𝒰 _
    ADANEdge v1 v2 vout r = ∑ λ t1 -> ∑ λ t2 -> ADANTreePath r ((_ , v1) , t1) × ADANTreeStep ((_ , v1) , t1) ((_ , v2) , t2) vout

-----------------------------------------
-- product theory specific


module _ (𝒯 : ProductTheory ℓ₀) {{_ : IShow (Sort 𝒯)}} where

  instance
    isSet-Str:ℬ× : isSet-Str (ℬ× 𝒯)
    isSet-Str:ℬ× = {!!}

  mutual
    constructTerms : ∀{n} {Γ : CtxHom (λ b _ -> SortTermᵈ 𝒯 b) n ◌}
                    -> {fst₁ : List (Sort 𝒯)}
                    -> {vs : Vec (⟨ F× 𝒯 n ⟩ (incl ◌-Free-𝐌𝐨𝐧)) (length fst₁)}
                    -> DVec (ANVecTree _ _ (ℬ× 𝒯) (F× 𝒯 n) (isWellTyped× 𝒯) (incl ◌-Free-𝐌𝐨𝐧)) vs
                    -> isSameCtx 𝒯 Γ fst₁ vs
                    -> CtxHom (Term₁-𝕋× 𝒯) (ι-Free-𝐌𝐨𝐧 fst₁) (map-Free-𝐌𝐨𝐧 (makeSort 𝒯) (asList Γ))
    constructTerms {fst₁ = ⦋⦌} [] P = ◌-⧜
    constructTerms {fst₁ = x ∷ fst₁} (x₁ ∷ ts) (.x ∷ P) = (incl (constructTerm x₁)) ⋆-⧜ constructTerms ts P

    constructTerm : ∀{n} {Γ : CtxHom (λ b _ -> SortTermᵈ 𝒯 b) n ◌} -> ∀{τ}
                    -> ANVecTree _ _ (ℬ× 𝒯) (F× 𝒯 n) (isWellTyped× 𝒯) (incl ◌) (_⊫_ 𝒯 Γ τ)
                    -> Term₁-𝕋× 𝒯 (map-Free-𝐌𝐨𝐧 (makeSort 𝒯) (asList Γ)) (makeSort 𝒯 τ)
    constructTerm (node1 (isNode (_ , _ , c)) .((𝒯 ⊫ _) (con _)) vs (conType .c x) ts) = con c (constructTerms ts x)
    constructTerm {Γ = Γ} {τ} (node1 (isVar x₂) .((𝒯 ⊫ _) _) ⦋⦌ (varType .x₂ atl) []) = var (map-∍ (makeSort 𝒯) P)
      where
        P : asList Γ ∍ τ
        P = atasList' Γ x₂ atl




