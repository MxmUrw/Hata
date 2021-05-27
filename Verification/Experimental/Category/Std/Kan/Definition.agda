
module Verification.Experimental.Category.Std.Kan.Definition where

open import Verification.Conventions
open import Verification.Experimental.Meta.Structure
open import Verification.Experimental.Set.Setoid.Definition
open import Verification.Experimental.Set.Setoid.Definition
open import Verification.Experimental.Set.Setoid.Instance.Category
open import Verification.Experimental.Data.Universe.Definition
open import Verification.Experimental.Category.Std.Category.Definition
open import Verification.Experimental.Category.Std.Category.Opposite
open import Verification.Experimental.Category.Std.Category.Instance.Category
open import Verification.Experimental.Category.Std.Functor.Definition
open import Verification.Experimental.Category.Std.Functor.Instance.Category
open import Verification.Experimental.Category.Std.Functor.Representable
open import Verification.Experimental.Category.Std.Morphism.Iso
open import Verification.Experimental.Category.Std.Natural.Definition
open import Verification.Experimental.Category.Std.Natural.Instance.Setoid

module _ {𝒞 : Category 𝑖} {𝒞' : Category 𝑗} {𝒟 : Category 𝑘} where
  module _ {p : Functor 𝒞 𝒞'} where
      instance
        isFunctor:◆-Cat : isFunctor ′(Functor 𝒞' 𝒟)′ ′(Functor 𝒞 𝒟)′ (p ◆-Cat_)
        isFunctor.map isFunctor:◆-Cat F = {!!}
        isFunctor.isSetoidHom:map isFunctor:◆-Cat = {!!}
        isFunctor.functoriality-id isFunctor:◆-Cat = {!!}
        isFunctor.functoriality-◆ isFunctor:◆-Cat = {!!}

module _ {𝒞 : Category 𝑖} {𝒞' : Category 𝑖} where
  module _ (p : Functor 𝒞 𝒞') where

    module _ {𝒟 : Category 𝑘} (F : Functor 𝒞 𝒟) where

      myF : Functor ′ Functor 𝒞' 𝒟 ′ (Std _)
      myF = ′( p ◆-Cat_ )′ ◆-Cat ′ [ F ,_]𝓈 ′

      Lan : 𝒰 _
      Lan = Corep myF



