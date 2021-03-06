
module Verification.Core.Order.DedekindCompletion.Definition where

open import Verification.Conventions
open import Verification.Core.Data.Int.Definition
open import Verification.Core.Data.Rational.Definition

open import Verification.Core.Algebra.Setoid
open import Verification.Core.Order.Linearorder

-- mostly from https://ncatlab.org/nlab/show/real+number
-- and https://ncatlab.org/nlab/show/Dedekind+cut



module _ {š : š ^ 3} (X : Linearorder š) where

  record isCut (L U : Subsetoid ā² āØ X ā© ā²) : š° š where
    constructor iscut
    field inhabited-ā© : ā¦ āØ L ā© ā¦
    field inhabited-ā© : ā¦ āØ U ā© ā¦
    field open-ā© : ā{a : āØ X ā©} -> āØ L ā© a -> ā Ī» (b : ā¦ āØ L ā© ā¦) -> a < āØ b ā©
    field open-ā© : ā{b : āØ X ā©} -> āØ U ā© b -> ā Ī» (a : ā¦ āØ U ā© ā¦) -> āØ a ā© < b
    field compare-Cut : ā{a b : āØ X ā©} -> a < b -> āØ L ā© a +-š° āØ U ā© b
    field by-ā©ā©-< : ā{a b : āØ X ā©} -> āØ L ā© a -> āØ U ā© b -> a < b

  open isCut {{...}} public

  record Cut : š° (((š .fst) āŗ) ā š ā 1 ā š ā 2) where
    constructor _,_
    field ā© : Subsetoid ā² āØ X ā© ā²
    field ā© : Subsetoid ā² āØ X ā© ā²
    field {{isCutProof}} : isCut ā© ā©

  open Cut public


module _ {š : š ^ 3} {X : Linearorder š} where
  _<L_ : āØ X ā© -> Cut X -> š° _
  _<L_ a (L , U) = āØ L ā© a

  _U<_ : Cut X -> āØ X ā© -> š° _
  _U<_ (L , U) b = āØ U ā© b

  infix 40 _U<_ _<L_ _<-Cut_

  _<-Cut_ : Cut X -> Cut X -> š° _
  _<-Cut_ x y = ā Ī» a -> (x U< a Ć-š° a <L y)

  instance
    isSetoid:Cut : isSetoid _ (Cut X)
    isSetoid.myRel isSetoid:Cut (Lā , Uā) (Lā , Uā) = (Lā ā¼ Lā) Ć-š° (Uā ā¼ Uā)
    isEquivRel.refl (isSetoid.isEquivRel:ā¼ isSetoid:Cut) = incl (refl , refl)
    isEquivRel.sym (isSetoid.isEquivRel:ā¼ isSetoid:Cut) (incl (p , q)) = incl (sym p , sym q)
    isEquivRel._ā_ (isSetoid.isEquivRel:ā¼ isSetoid:Cut) (incl (p0 , q0)) (incl (p1 , q1)) = incl (p0 ā p1 , q0 ā q1)


  disjoint-ā©ā© : ā{ā©a ā©a} -> {{_ : isCut X ā©a ā©a}} -> ā{x} -> āØ ā©a ā© x -> āØ ā©a ā© x -> š-š°
  disjoint-ā©ā© p q = irrefl-< (by-ā©ā©-< p q)

  closed-ā© : ā{ā©a ā©a} -> {{_ : isCut X ā©a ā©a}} -> ā{x y} -> (x < y) -> āØ ā©a ā© y -> āØ ā©a ā© x
  closed-ā© {ā©a} {ā©a} {x} {y} x<y y-ā©a = case compare-Cut x<y of
                   (Ī» (p : āØ ā©a ā© x) -> p)
                   (Ī» (p : āØ ā©a ā© y) -> š-rec (disjoint-ā©ā© y-ā©a p))

  closed-ā© : ā{ā©a ā©a} -> {{_ : isCut X ā©a ā©a}} -> ā{x y} -> (x < y) -> āØ ā©a ā© x -> āØ ā©a ā© y
  closed-ā© {ā©a} {ā©a} {x} {y} x<y x-ā©a = case compare-Cut x<y of
                   (Ī» (p : āØ ā©a ā© x) -> š-rec (disjoint-ā©ā© p x-ā©a))
                   (Ī» (p : āØ ā©a ā© y) -> p)

