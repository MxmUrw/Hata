
module Verification.Old.Core.Category.Limit.Kan.Local where

open import Verification.Conventions
open import Verification.Old.Core.Category.Definition
open import Verification.Old.Core.Category.Instance.Cat
open import Verification.Old.Core.Category.Instance.Type
open import Verification.Old.Core.Category.Quiver
open import Verification.Old.Core.Category.FreeCategory
open import Verification.Old.Core.Category.Iso
open import Verification.Old.Core.Category.Proper
open import Verification.Old.Core.Category.Functor.Adjunction
open import Verification.Old.Core.Category.Instance.Functor
open import Verification.Old.Core.Category.Functor.Presheaf
open import Verification.Old.Core.Category.Functor.Representable
open import Verification.Old.Core.Category.Lift
open import Verification.Old.Core.Category.Limit.Kan.Terminal
open import Verification.Old.Core.Category.Limit.Kan.Equalizer
open import Verification.Old.Core.Category.Limit.Kan.Definition
open import Verification.Old.Core.Homotopy.Level
open import Verification.Old.Core.Algebra.Basic.Monoid
open import Verification.Old.Core.Order.Lattice
open import Verification.Old.Core.Order.Instance.Level
open import Verification.Old.Core.Order.Instance.Product

-- module _ {S : Category 𝑗} {𝒞 : Category 𝑖} where

--   llim' : (F : Functor S 𝒞) -> PSh 𝒞 (𝑖 ⌄ 1)
--   llim' F = {!!}


private
  Fun[_,_] = Category:Functor

  infixl 70 _◇_
  _◇_ = comp-Cat


instance
  I1Category:Functor : ∀{𝒟 : Category 𝑘} {{_ : I1Category 𝒟}} -> ∀{𝒞 : Category 𝑖} -> I1Category Fun[ 𝒞 , 𝒟 ]
  I1Category:Functor = {!!}

module _ {𝒞 : Category 𝑖} {𝒞' : Category 𝑖} {𝒟 : Category 𝑘} {{_ : I1Category 𝒟}} where
  hasLan : ∀(F : Functor 𝒞 𝒟) -> (p : Functor 𝒞 𝒞') -> 𝒰 _
  hasLan F p =.Old.Core.resentation ((p *) ◇ Functor:Hom F)

  isLan : ∀(F : Functor 𝒞 𝒟) -> (p : Functor 𝒞 𝒞') -> Functor 𝒞' 𝒟 -> 𝒰 _
  isLan F p = .Old.Core.resentation ((p *) ◇ Functor:Hom F)

  hasRan :  ∀(F : Functor 𝒞 𝒟) -> (p : Functor 𝒞 𝒞') -> 𝒰 _
  hasRan F p = Representation (mirror-Functor (p *) ◇ Functor:Homᵒᵖ F)

  isRan : ∀(F : Functor 𝒞 𝒟) -> (p : Functor 𝒞 𝒞') -> Functor 𝒞' 𝒟 -> 𝒰 _
  isRan F p = IRepresentation (mirror-Functor (p *) ◇ Functor:Homᵒᵖ F)

module _ {S : Category 𝑖} {𝒞 : Category 𝑖} {{_ : I1Category 𝒞}} where
  isLimit : (D : Functor S 𝒞) -> ⟨ 𝒞 ⟩ -> 𝒰 _
  isLimit D x = isRan D (! S) (Diagram-𝟙 x)

  isColimit : (D : Functor S 𝒞) -> 𝟙 ⟶ 𝒞 -> 𝒰 _
  isColimit D x = isLan D (! S) x


  module _ {{_ : has(S)ShapedLimits 𝒞}} where
    instance
      Limit→localLimit : {D : Functor S 𝒞} -> isLimit D (lim D)
      ⟨ rep Limit→localLimit ⟩ = {!!}
      of rep Limit→localLimit = {!!}

  module _ {{L : has(S)ShapedColimits 𝒞}} where
    instance
      Colimit→localColimit : {D : Functor S 𝒞} -> isColimit D (colim-D D)
      ⟨ ⟨ ⟨ corep Colimit→localColimit ⟩ ⟩ ⟩ f =
        let F = free⁻¹ {{of L}}
            Ff = F f
        in Ff
      of ⟨ ⟨ corep Colimit→localColimit ⟩ ⟩ = record {}
      of ⟨ corep Colimit→localColimit ⟩ = {!!}
      ⟨ ⟨ inverse (of corep Colimit→localColimit) ⟩ ⟩ f = free f
      of ⟨ inverse (of corep Colimit→localColimit) ⟩ = record {}
      of inverse (of corep Colimit→localColimit) = {!!}
      /⟲ (of corep Colimit→localColimit) = {!!}
      /⟳ (of corep Colimit→localColimit) = {!!}

  module _ {D : Functor S 𝒞} {x : ⟨ 𝒞 ⟩} {{L : isLimit D x}} where
    cone : ⟨ ! S * ⟩ ` x ` ⟶ D
    cone = ⟨ ⟨ ⟨ rep L ⟩ ⟩ ⟩ id

  module _ {D : Functor S 𝒞} {x : 𝟙 ⟶ 𝒞} {{L : isColimit D x}} where
    cocone : D ⟶ ⟨ ! S * ⟩ x
    cocone = ⟨ ⟨ ⟨ corep L ⟩ ⟩ ⟩ id

    elim-colim : {y : ⟨ 𝒞 ⟩} -> (D ⟶ ⟨ ! S * ⟩ ` y `) -> ⟨ x ⟩ (↥ tt) ⟶ y
    elim-colim {y} F = ⟨ ⟨ ⟨ inverse (of corep L) ⟩ {` y `} ⟩ F ⟩ {↥ tt}
