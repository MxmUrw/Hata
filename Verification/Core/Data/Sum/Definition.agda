
module Verification.Core.Data.Sum.Definition where

open import Verification.Conventions
open import Verification.Core.Set.Function.Injective
-- open import Verification.Core.Category.Definition
-- open import Verification.Core.Category.EpiMono
-- open import Verification.Core.Category.Instance.Type


macro
  _+_ : β{π π : π} {π π : π ^ 2} -> (π° π) [ π ]β (π° π) [ π ]β SomeStructure
  _+_ = Ξ»str A β¦ Ξ»str B β¦ #structureOn (A +-π° B)
  infixr 40 _+_

macro
  _+β§Ώ : β{π π : π} {π : π ^ 2} -> (π° π) [ π ]β SomeStructure
  _+β§Ώ {π = π} = Ξ»str A β¦ #structureOn (Ξ» (B : π° π) -> A +-π° B)
  infix 40 _+β§Ώ

private instance _ = isSetoid:byId
private instance _ = isSetoid:byPath

module _ {A : π°' β} {B : π°' β'} where
  split-+-Str : (x : A + B) -> (β Ξ» (a : A) -> x β‘-Str left a) + (β Ξ» b -> x β‘-Str right b)
  split-+-Str (left x) = left (x , refl)
  split-+-Str (just x) = right (x , refl)

  split-+ : (x : A + B) -> (β Ξ» (a : A) -> x β‘ left a) + (β Ξ» b -> x β‘ right b)
  split-+ (left x) = left (x , refl)
  split-+ (just x) = right (x , refl)

  cancel-right : (b : B) -> (A + B) -> B
  cancel-right b (left x) = b
  cancel-right b (right x) = x

  cancel-left : (a : A) -> (A + B) -> A
  cancel-left a (left x) = x
  cancel-left a (right x) = a

  either : {C : π°' π} -> (A -> C) -> (B -> C) -> (A +-π° B) -> C
  either f g (left x) = f x
  either f g (just x) = g x

  rec-+ = either

_β’_ : β{A : π° β} (a b : A) -> π° β
a β’ b = (a β‘ b) -> π-π°

module _ {A : π° β} {B : π° β'} where
  leftβ’right : β{a : A}{b : B} -> left a β’ right b
  leftβ’right p = transport (cong f p) tt
    where f : A + B -> π°β
          f (left x) = π-π°
          f (right x) = π-π°

  rightβ’left : β{a : A}{b : B} -> right b β’ left a
  rightβ’left = Ξ» p -> leftβ’right (sym p)


module _ {A : π° π} {B : π° π} {C : π° π} {D : π° π} where
  map-+ : β(f : A -> B) (g : C -> D) -> (A + C) -> (B + D)
  map-+ f g = either (Ξ» x -> left (f x)) (Ξ» y -> right (g y))

module _ {A : π° π} {B : π° π} {C : π° π} where
  mapLeft : β(f : A -> B) -> (A + C) -> (B + C)
  mapLeft f = either (Ξ» x -> left (f x)) right

  mapRight : β(f : A -> B) -> (C + A) -> (C + B)
  mapRight f = either left (Ξ» x -> right (f x))

module _ {A : π° π} {B : π° π} where
  instance
    isInjective:left : isInjective-π° (left {A = A} {B = B})
    isInjective-π°.cancel-injective-π° isInjective:left {a} {b} = {!!} -- refl-StrId = refl

  instance
    isInjective:right : isInjective-π° (right {A = A} {B = B})
    isInjective-π°.cancel-injective-π° isInjective:right {a} {b} = {!!} -- refl-StrId = refl


module _ {A : π° π} {B : π° π} {C : π° π} {D : π° π} where
  instance
    isInjective-π°:either : {f : A -> C} {g : B -> C} -> {{_ : isInjective-π° f}} {{_ : isInjective-π° g}} -> isInjective-π° (map-+ f g)
    isInjective-π°:either = {!!}


module _ {A : π° π} {B : π° π} where
  instance
    IShow:+-π° : {{_ : IShow A}} {{_ : IShow B}} -> IShow (A + B)
    IShow:+-π° = record { show = either show show }

    -- isInjective-π°.injective (isInjective-π°:either {f} {g}) {left x} {left xβ} p = cong-Str left (injective (injective {{isInjective-π°:left}} p))
    -- isInjective-π°.injective (isInjective-π°:either {f} {g}) {just x} {just xβ} p = cong-Str right (injective (injective {{isInjective-π°:right}} p))


module _ {A : π° π} {B : π° π} {{_ : isSetoid {πβ} A}} {{_ : isSetoid {πβ} B}} where
  instance
    isSetoid:+ : isSetoid (A + B)
    isSetoid:+ = isSetoid:byDef
      (Ξ» {(left a) (left b)  β Lift {πβ ο½€ πβ} {πβ} (a βΌ b)
         ;(left a) (right b) β β₯-π°
         ;(right a) (left b) β β₯-π°
         ;(right a) (right b) β Lift {πβ ο½€ πβ} {πβ} (a βΌ b)
         })
      (Ξ» { {left a}  β β₯ refl
         ; {right a} β β₯ refl
         })
      {!!}
      {!!}


-- isSetoid:byDef (Ξ» (aβ , bβ) (aβ , bβ) -> (aβ βΌ aβ) Γ (bβ βΌ bβ))
                 -- (refl , refl)
                 -- (Ξ» (p , q) -> (p β»ΒΉ , q β»ΒΉ))
                 -- (Ξ» (pβ , qβ) (pβ , qβ) -> (pβ β pβ , qβ β qβ))


{-
  isInjective:left : β{a b : A} -> left {B = B} a β‘ left b -> a β‘ b
  isInjective:left {a = a} p = cong (cancel-left a) p

  isInjective:right : β{a b : B} -> right {A = A} a β‘ right b -> a β‘ b
  isInjective:right {a = a} p = cong (cancel-right a) p

module _ {A B : π° β} where
  instance
    IMono:left : IMono (left {A = A} {B = B})
    IMono.isMono IMono:left g h p = funExt (Ξ» x -> isInjective:left (Ξ» i -> p i x))

  instance
    IMono:right : IMono (right {A = A} {B = B})
    IMono.isMono IMono:right g h p = funExt (Ξ» x -> isInjective:right (Ξ» i -> p i x))
    -}
