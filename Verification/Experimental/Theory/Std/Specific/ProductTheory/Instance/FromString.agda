
module Verification.Experimental.Theory.Std.Specific.ProductTheory.Instance.FromString where

open import Verification.Conventions hiding (_⊔_)
open import Verification.Experimental.Theory.Std.Specific.ProductTheory.Definition
open import Verification.Experimental.Theory.Std.Presentation.Token.Definition


UntypedCon : ProductTheory 𝑖 -> 𝒰 _
UntypedCon 𝒯 = ∑ λ xs -> ∑ λ x -> Con 𝒯 xs x


parseTokenTree : (𝒯 : ProductTheory ℓ₀) -> TokenDefinition (UntypedCon 𝒯) -> Tree (UntypedCon 𝒯) String -> String +-𝒰 (∑ λ xs -> ∑ λ x -> Term₁-𝕋× 𝒯 xs x)
parseTokenTree 𝒯 Def t = left "not implemented!"



module _ {𝒯 : ProductTheory ℓ₀} {{Def : TokenDefinition (UntypedCon 𝒯)}} where
  private
    getTerm : String -> String +-𝒰 (∑ λ xs -> ∑ λ x -> Term₁-𝕋× (𝒯) xs x)
    getTerm s =
      let t = parseTokens Def s
      in parseTokenTree _ Def t

  instance
    fromString:ProductTheory : FromString (∑ λ xs -> ∑ λ x -> Term₁-𝕋× 𝒯 xs x)
    fromString:ProductTheory = record { fromString = getTerm }



