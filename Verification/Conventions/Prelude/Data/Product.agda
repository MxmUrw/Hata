

module Verification.Conventions.Prelude.Data.Product where

open import Verification.Conventions.Proprelude
open import Verification.Conventions.Prelude.Classes
open import Verification.Conventions.Prelude.Data.String
open import Verification.Conventions.Prelude.Data.Maybe
open import Verification.Conventions.Prelude.Data.Nat
open import Verification.Conventions.Prelude.Data.Fin

variable m n k : β

instance
  IShow:Γ : β{A B : π° π} -> {{_ : IShow A}} {{_ : IShow B}} -> IShow (A Γ-π° B)
  IShow.show IShow:Γ (a , b) = "(" <> show a <> " , " <> show b <> ")"


_^-π°_ : π° π -> β -> π° π
A ^-π° zero = Lift π-π°
A ^-π° suc zero = A
A ^-π° suc (suc n) = A Γ-π° (A ^-π° (suc n))

_β-π°_ : β{A : π° π} -> {n : β} -> (A ^-π° suc n) -> Fin-R (suc n) -> A
_β-π°_ {n = zero} x zero = x
_β-π°_ {n = suc n} (x , xs) zero = x
_β-π°_ {n = suc n} (x , xs) (suc i) = _β-π°_ xs i


instance
  Exponent-Notation:π°,β,π° : Exponent-Notation (π° π) β (β (π° π))
  (Exponent-Notation:π°,β,π° Exponent-Notation.^ x) n = _^-π°_ x n

_βE_ : β{A : π° π} -> β{n} -> (A ^ (suc n)) -> (i : β) -> {{_ : i β€-β-Dec n}} -> (A)
_βE_ x i {{p}} = x β-π° (β€βFin {{p}})

-- instance
  -- Index-Notation:^-π°,β,A : β{A : π° π} -> β{n} -> Index-Notation (A ^ (suc n)) (β β) (Ξ» i -> i β€-β-Dec n) (β A)
  -- Index-Notation._β_ Index-Notation:^-π°,β,A x i {{p}} = x βE i


---------------------------------------------------------------
-- new ellipsis based indexing

record Ellipsis (A : π° π) : π° π where
  constructor _β―_
  field fstEllipsis : A
  field sndEllipsis : A
infix 200 _β―_

open Ellipsis public

record GoodEllipsis (e : Ellipsis β) (max : β) : π°β where
  instance constructor goodEllipsis
  field {{fstProp}} : fstEllipsis e β€-β-Dec sndEllipsis e
  field {{sndProp}} : sndEllipsis e β€-β-Dec max

private
  size : Ellipsis β -> β
  size (a β― b) = b βΈ a


βEllipsis : β{A : π° π} -> β{n} -> (A ^ (suc n)) -> (e : Ellipsis β) -> {{_ : GoodEllipsis e n}} -> (A ^ suc (size e))
βEllipsis {n = zero} a (.zero β― .zero) β¦ goodEllipsis β¦ zero β¦ β¦ zero β¦ β¦ = a
βEllipsis {n = suc n} (a , _) (.zero β― .zero) β¦ goodEllipsis β¦ zero β¦ β¦ zero β¦ β¦ = a
βEllipsis (a , as) (.zero β― (suc n)) β¦ goodEllipsis β¦ zero β¦ β¦ suc β¦ β¦ = a , βEllipsis as (0 β― n)
βEllipsis (a , as) ((suc m) β― (suc n)) β¦ goodEllipsis {{suc}} {{suc}} β¦ = βEllipsis as (m β― n)
-- {{goodEllipsis {{it}} {{Q}}}}

instance
  Index-Notation:TupleEllipsis : β{A : π° π} -> β{n} -> Index-Notation (A ^ (suc n)) (const (Ellipsis β)) (Ξ» e -> GoodEllipsis e n) (Ξ» (_ , e) -> A ^ suc (size e))
  Index-Notation._β_ Index-Notation:TupleEllipsis = βEllipsis


instance
  fromNatEllipsis : HasFromNat (Ellipsis β)
  fromNatEllipsis = record { Constraint = const π-π° ; fromNat = Ξ» n β n β― n }




