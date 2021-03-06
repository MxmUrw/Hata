
module Verification.Core.Theory.Std.Specific.Simple.LambdaChurch.Definition where

open import Verification.Core.Conventions hiding (isSet)
open import Verification.Core.Data.Fin.Definition
open import Verification.Core.Set.Set.Definition
open import Verification.Core.Set.Setoid
open import Verification.Core.Data.Universe.Definition
open import Verification.Core.Data.Universe.Instance.Category
open import Verification.Core.Order.Preorder
open import Verification.Core.Order.Lattice
open import Verification.Core.Theory.Std.Presentation.Signature.SingleSorted.Definition as SingleSorted
open import Verification.Core.Theory.Std.Generic.TypeTheory.Definition
open import Verification.Core.Theory.Std.Generic.TypeTheory.Simple

-- data TySig : â -> ð°â where
--   `â` `ð¹` : TySig 0
--   `â` : TySig 2


-- Defining types

-- Ty-Î» : ð°â -> ð°â
-- Ty-Î» = SingleSorted.Term TySig

-- infixr 50 _â_
-- pattern _â_ Ï Ï = te `â` (Ï â· Ï â· [])


data Ty-Î» {ð} : ð° ð where
  `â` `ð¹` : Ty-Î»
  _`â`_ : Ty-Î» {ð} -> Ty-Î» {ð} -> Ty-Î»



data Term-Î» : â -> ð°â where
  app : (f g : Term-Î» n) -> Term-Î» n
  lam : Ty-Î» -> (t : Term-Î» (suc n)) -> Term-Î» n
  var : ð½Ê³ n -> Term-Î» n
  zero : Term-Î» n
  suc : Term-Î» n -> Term-Î» n
  false true : Term-Î» n
  rec-â : Ty-Î» -> Term-Î» (suc n) -> Term-Î» n -> Term-Î» n -> Term-Î» n

-- data SCtx (A : ð°â) : ð°â where
--   [] : SCtx A
--   _,_ : SCtx A -> Ty-Î» A -> SCtx A


instance
  IBootEq:â¥ : â{ð} -> IBootEq {ð} (Ty-Î»)
  IBootEq._â_ IBootEq:â¥ = f
    where f : Ty-Î» â Ty-Î» â Bool
          f `â` `â` = true
          f `ð¹` `ð¹` = true
          f (a `â` aâ) (b `â` bâ) = f a b and f aâ bâ
          f _ _ = false

-- instance
--   IBootEq:SCtx : â{A} -> {{_ : IBootEq A}} -> IBootEq (SCtx A)
--   IBootEq:SCtx = {!!}

-- instance
--   IBootEq:TySig : IBootEq (TySig n)
--   IBootEq:TySig = {!!}

-- instance
--   IBootEq:Term : â{A Ï} -> {{_ : IBootEq A}} -> {{â {n} -> IBootEq (Ï n)}} -> IBootEq (SingleSorted.Term {ð} Ï A)
--   IBootEq:Term = {!!}

-- Info : ð°â
-- Info = Jdg-â¦¿ (Ty-Î» â¥)
-- -- (SCtx â¥) 

-- Statement : ð°â
-- Statement = â Î» n -> Jdg-â¦¿ (Ty-Î» (Fin n))
-- -- (SCtx (Fin n)) 

-- instance
--   isSet:Statement : isSet Statement
--   isSet:Statement = record { fillPath-Set = {!!} }

-- instance
--   isSetoid:Term : isSetoid _ Term-Î»
--   isSetoid:Term = isSetoid:byDef _â£_

-- data ÏVar : â{A} -> â -> SCtx A -> Ty-Î» A -> ð°â where
--   zero : â{A} -> â{Î : SCtx A} -> {Ï : Ty-Î» A} -> ÏVar 0 (Î , Ï) Ï
--   suc : â{A n} -> â{Î : SCtx A} -> {Ï Ï : Ty-Î» A} -> ÏVar n Î Ï -> ÏVar (suc n) (Î , Ï) Ï

-- data _â¶_â¢_ : â{A} -> Term-Î» -> SCtx A -> Ty-Î» A -> ð°â where
--   var : â{A n} -> â{Î : SCtx A} {Ï : Ty-Î» A} -> ÏVar n Î Ï -> (var n) â¶ Î â¢ Ï
--   app : â{A} -> â{t s} -> â{Î : SCtx A} {Ï Ï : Ty-Î» A} -> (t â¶ Î â¢ Ï â Ï) -> (s â¶ Î â¢ Ï) -> (app s t â¶ Î â¢ Ï)
--   lam : â{A} -> â{t} -> â{Î : SCtx A} {Ï Ï : Ty-Î» A} -> (t â¶ (Î , Ï) â¢ Ï) -> (lam t â¶ Î â¢ Ï â Ï)


