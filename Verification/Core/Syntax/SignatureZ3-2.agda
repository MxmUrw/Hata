
module Verification.Core.Syntax.SignatureZ3-2 where

open import Verification.Conventions hiding (k)
open import Verification.Core.Category
open import Verification.Core.Order
open import Verification.Core.Type
open import Verification.Core.Category.Monad
open import Verification.Core.Category.Instance.Kleisli
open import Verification.Core.Category.Instance.IdxSet
open import Verification.Core.Category.Limit.Specific
open import Verification.Core.Category.Limit.Kan
open import Verification.Core.Syntax.SignatureZ3
-- open import Verification.Unification.RecAccessible


module _ {K : 𝒰₀} where
  module _ {σ : Signature} {V : K -> 𝒰₀} where
    commutes:join∣join-te : {ks : Vec K (suc n)} -> ∀{k} -> (s : σ k ks) -> (ts : Termsᵥ σ (Term σ V) ks) -> join-Term (join-te s (forget-Terms ts)) ≡ join-te s (join-Termsᵥ ts)
    commutes:join∣join-te s ts with split-+-Str (reduce-Terms (forget-Terms ts)) | split-+-Str (reduce-Terms (join-Termsᵥ ts))
    ... | left x | left x₁ = refl
    ... | left (x , _) | just x₁ = 𝟘-rec (¬isFail-forget-Terms _ x)
    ... | just x | left x₁ = {!!}
    ... | just ((x , xP) , xQ) | just ((y , yP) , yQ) with split-+-Str (reduce-Terms (join-Termsᵥ x))
    ... | left x₁ = {!!}
    ... | just ((z , zP) , zQ) with (isInjective:forget-Terms (≡→≡-Str xP))
    ... | refl-StrId with (isInjective:forget-Terms (≡→≡-Str (yP ∙ zP ⁻¹)))
    ... | refl-StrId = refl


    join-assoc-Term : ∀{k} -> (x : Term σ (Term σ (Term σ V)) k) → join-Term (join-Term x) ≡ join-Term (map-Term join-Term x)
    join-assoc-Term (te s ts) = join-Term (join-te s (join-Termsᵥ ts)) ≡⟨ {!!} ⟩
                                join-Term (join-te s (forget-Terms (map-Termsᵥ join-Term ts))) ≡⟨ commutes:join∣join-te s (map-Termsᵥ join-Term ts) ⟩
                                join-te s (join-Termsᵥ (map-Termsᵥ join-Term ts)) ∎
    join-assoc-Term (var x) = refl
    join-assoc-Term fail = refl




