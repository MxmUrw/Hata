
module Verification.Experimental.Data.Indexed.Property.Iso where

open import Verification.Conventions

open import Verification.Experimental.Set.Setoid.Definition
open import Verification.Experimental.Set.Decidable
open import Verification.Experimental.Set.Contradiction
open import Verification.Experimental.Category.Std.Category.Definition
open import Verification.Experimental.Category.Std.Morphism.Iso
open import Verification.Experimental.Category.Std.Morphism.EpiMono
open import Verification.Experimental.Data.Universe.Definition
open import Verification.Experimental.Data.Product.Definition
open import Verification.Experimental.Data.Sum.Definition
open import Verification.Experimental.Category.Std.Category.Structured.SeparatingFamily
open import Verification.Experimental.Category.Std.Limit.Specific.Coproduct.Definition
open import Verification.Experimental.Data.Universe.Instance.Category

open import Verification.Experimental.Data.Universe.Definition
open import Verification.Experimental.Data.Universe.Everything
open import Verification.Experimental.Data.Indexed.Definition



module _ {𝒞 : Category 𝑖} {I : 𝒰 𝑗} where
  module _ {a b : 𝐈𝐱 I 𝒞} where
    construct-≅-𝐈𝐱 : (∀ {i} -> ix a i ≅ ix b i) -> a ≅ b
    construct-≅-𝐈𝐱 f = f' since Q
      where
        f' : a ⟶ b
        f' = λ i → ⟨ f {i} ⟩

        g' : b ⟶ a
        g' = λ i → inverse-◆ (of f {i})

        Q = record
            { inverse-◆ = g'
            ; inv-r-◆   = λ i -> inv-r-◆ (of f)
            ; inv-l-◆   = λ i -> inv-l-◆ (of f)
            }



