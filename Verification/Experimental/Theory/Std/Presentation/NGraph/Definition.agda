
module Verification.Experimental.Theory.Std.Presentation.NGraph.Definition where


open import Verification.Conventions
open import Verification.Experimental.Set.Function.Surjective
open import Verification.Experimental.Algebra.Monoid.Definition
open import Verification.Experimental.Data.Product.Definition
open import Verification.Experimental.Data.Sum.Definition
open import Verification.Experimental.Data.Nat.Free
open import Verification.Experimental.Data.Sum.Instance.Functor
open import Verification.Experimental.Data.Universe.Everything
open import Verification.Experimental.Category.Std.Category.Definition
open import Verification.Experimental.Category.Std.Functor.Definition


module _ (N : 𝒰 𝑖) (size : N -> 人ℕ) where
  record isNGraph (V : 𝒰 𝑗) : 𝒰 (𝑖 ､ 𝑗) where
    field node : V -> N
    field neigh : (v : V) -> [ size (node v) ]ᶠ -> V

  open isNGraph {{...}} public

  module _ {𝑗 : 𝔏} where
    NGraph = (𝒰 𝑗) :& isNGraph

  module _ {ℬ : Category 𝑘} (F : Functor ℬ (𝐔𝐧𝐢𝐯 𝑙)) where
    record isANG (G : NGraph {𝑗}) : 𝒰 (𝑖 ､ 𝑗 ､ 𝑘 ､ 𝑙) where
      field bo : ⟨ G ⟩ -> ⟨ ℬ ⟩
      field ann : (v : ⟨ G ⟩) -> [ size (node v) ]ᶠ -> ⟨ F ⟩ (bo v)



    record isConstantANG (b₀ : ⟨ ℬ ⟩) (G : NGraph {𝑗}) : 𝒰 (𝑖 ､ 𝑗 ､ 𝑘 ､ 𝑙) where
      -- field b₀ : ⟨ ℬ ⟩
      field ann : (v : ⟨ G ⟩) -> [ size (node v) ]ᶠ -> ⟨ F ⟩ (b₀)

    open isConstantANG {{...}} public

    record TypingAnnotation (𝑗 : 𝔏) : 𝒰 (𝑖 ､ 𝑘 ､ 𝑙 ､ 𝑗 ⁺) where
      field isOfType : (b : ⟨ ℬ ⟩) -> (n : N) -> ([ size n ]ᶠ -> ⟨ F ⟩ b) -> 𝒰 𝑗

    open TypingAnnotation public

    module _ {G : NGraph {𝑗}} {b₀} {{_ : isConstantANG b₀ G}} where
      record isContracted : 𝒰 (𝑖 ､ 𝑗 ､ 𝑘 ､ 𝑙) where
        field iscontr : ∀{v w : ⟨ G ⟩}
                        -> (iv : [ size (node v) ]ᶠ )
                        -> (iw : [ size (node w) ]ᶠ )
                        -> neigh v iv ≡ w
                        -> neigh w iw ≡ v
                        -> ann v iv ≡ ann w iw

      open isContracted {{...}} public

      record isWellTyped (TA : TypingAnnotation 𝑖₁) : 𝒰 (𝑖 ､ 𝑖₁ ､ 𝑗 ､ 𝑘 ､ 𝑙) where
        field hasType : (v : ⟨ G ⟩) -> isOfType TA b₀ _ (ann v)

      open isWellTyped {{...}} public

--   record isAnnGraph (E : 𝒰 𝑘) (V : 𝒰 𝑘) : 𝒰 (𝑖 ､ 𝑗 ､ 𝑘) where
--     constructor anngraph
--     field bo : V -> ⟨ ℬ ⟩
--     field source : E -> ∑ λ v -> ⟨ F ⟩ (bo v)
--     field target : E -> ∑ λ v -> ⟨ F ⟩ (bo v)

--   open isAnnGraph {{...}} public

--   AnnGraph : (E : 𝒰 𝑘) -> _
--   AnnGraph E = _ :& isAnnGraph E





