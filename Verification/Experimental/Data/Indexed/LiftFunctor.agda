
module Verification.Experimental.Data.Indexed.LiftFunctor where

open import Verification.Experimental.Conventions

open import Verification.Experimental.Algebra.Monoid.Free.Definition
open import Verification.Experimental.Data.Nat.Free
open import Verification.Experimental.Set.Setoid.Definition
open import Verification.Experimental.Set.Set.Definition
open import Verification.Experimental.Set.Contradiction
open import Verification.Experimental.Set.Set.Instance.Category
open import Verification.Experimental.Category.Std.Category.Definition
open import Verification.Experimental.Category.Std.Functor.Definition
open import Verification.Experimental.Category.Std.Morphism.Iso
open import Verification.Experimental.Category.Std.Functor.Adjoint
open import Verification.Experimental.Category.Std.Functor.Adjoint.Property.Preservation

open import Verification.Experimental.Data.Universe.Definition
open import Verification.Experimental.Data.Universe.Everything
open import Verification.Experimental.Data.Indexed.Definition



module _ {𝒞 : Category 𝑖} {𝒟 : Category 𝑗} {I : 𝒰 𝑘} where

  liftFunctor-𝐈𝐱 : (∀(i : I) -> Functor 𝒞 𝒟) -> Functor (𝐈𝐱 I 𝒞) (𝐈𝐱 I 𝒟)
  liftFunctor-𝐈𝐱 Fs = F since P
    where
      F : (𝐈𝐱 I 𝒞) -> (𝐈𝐱 I 𝒟)
      F x = indexed (λ i → ⟨ Fs i ⟩ (ix x i))

      map-F : ∀{a b : 𝐈𝐱 I 𝒞} -> (f : a ⟶ b) -> F a ⟶ F b
      map-F f i = map {{of Fs i}} (f i)

      P : isFunctor _ _ F
      isFunctor.map P = map-F
      isFunctor.isSetoidHom:map P = {!!}
      isFunctor.functoriality-id P = {!!}
      isFunctor.functoriality-◆ P = {!!}




