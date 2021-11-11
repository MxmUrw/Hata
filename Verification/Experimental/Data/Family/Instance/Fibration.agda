
module Verification.Core.Data.Family.Instance.Fibration where

open import Verification.Core.Conventions
open import Verification.Core.Data.Family.Definition

open import Verification.Core.Set.Setoid.Definition
open import Verification.Core.Set.Set.Definition
open import Verification.Core.Set.Set.Instance.Category
open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Category.Std.Functor.Definition

open import Verification.Core.Data.Universe.Definition
open import Verification.Core.Data.Universe.Everything

open import Verification.Core.Category.Std.Fibration.Definition

module _ {𝒞 : Category 𝑗} {𝑖} where
  private
    Forget : 𝐅𝐚𝐦 𝒞 𝑖 -> 𝐓𝐲𝐩𝐞 _
    Forget 𝔔 = ⟨ 𝔔 ⟩

  instance
    Register:ForgetFam = register[ "" ] Forget

  instance
    isFunctor:ForgetFam : isFunctor (𝐅𝐚𝐦 𝒞 𝑖) (𝐓𝐲𝐩𝐞 _) Forget
    isFunctor.map isFunctor:ForgetFam = λ f -> ⟨ f ⟩
    isFunctor.isSetoidHom:map isFunctor:ForgetFam = {!!}
    isFunctor.functoriality-id isFunctor:ForgetFam = {!!}
    isFunctor.functoriality-◆ isFunctor:ForgetFam = {!!}

  instance
    isFibration:ForgetFam : isFibration (𝐅𝐚𝐦 𝒞 𝑖) (𝐓𝐲𝐩𝐞 _) ′ Forget ′
    isFibration:ForgetFam = {!!}



