
{-# OPTIONS --cubical --allow-unsolved-metas #-}

module Verification.VHM3.Old.Core.Type.FinFam where

open import Verification.VHM3.Old.Core.Base
open import Verification.VHM3.Old.Core.Meta
open import Verification.VHM3.Old.Core.Notation
open import Verification.VHM3.Old.Core.Algebra.Basic.Monoid
open import Verification.VHM3.Old.Core.Space.Order
open import Verification.VHM3.Old.Core.Type
open import Verification.VHM3.Old.Core.Category.Base
open import Verification.VHM3.Old.Core.Category.Instance.Type
open import Verification.VHM3.Old.Core.Category.Instance.TypeProperties
open import Verification.VHM3.Old.Core.Category.Instance.Cat
open import Verification.VHM3.Old.Core.Category.Instance.CatProperties
open import Verification.VHM3.Old.Core.Category.Limit
open import Verification.VHM3.Old.Core.Category.Idempotent

--------------------------------------------------------------------
-- == Normed type

record INormed (V : Totalorder 𝑖) (A : 𝒰 𝑗) : 𝒰 (𝑖 ⊔ 𝑗) where
  field size : A -> ⟨ V ⟩
open INormed {{...}} public

instance
  INotation:Absolute:INormed : ∀{V : Totalorder 𝑖} {A : 𝒰 𝑗} {{_ : INormed V A}} -> INotation:Absolute A ⟨ V ⟩
  INotation:Absolute.∣ INotation:Absolute:INormed ∣ = size



module _ (A : Totalorder⍮Dec 𝑖) (V : Monoid 𝑖) where
  private
    AV = ⟨ A ⟩ × ⟨ V ⟩
  PreFinFam = List AV

  size-PreFinFam : PreFinFam -> ⟨ A ⟩ +-𝒰 Lift {j = 𝑖} ⊤
  size-PreFinFam [] = right (lift tt)
  size-PreFinFam ((a , v) ∷ xs) = min (left a) (size-PreFinFam xs)

  instance
    INormed:PreFinFam : INormed ((⌘ ⟨ A ⟩) ⊕ (⌘ Lift ⊤)) PreFinFam
    INormed.size INormed:PreFinFam = size-PreFinFam

  insert : AV -> PreFinFam -> PreFinFam
  insert (a , v) [] = (a , v) ∷ []
  insert (a , av) ((x , xv) ∷ xs) with a < x ？ | (a ≡ x) ？
  ... | P | right x₁ = (a , av ⋅ xv) ∷ xs
  ... | left x₂ | left x₁ = (x , xv) ∷ insert (a , av) xs
  ... | right x₂ | left x₁ = (a , av) ∷ (x , xv) ∷ xs

  sort : PreFinFam -> PreFinFam
  sort [] = []
  sort (x ∷ xs) = insert x (sort xs)

  instance
    IIdempotent:sort : IIdempotent sort
    IIdempotent./idempotent IIdempotent:sort = {!!}

  FinFam = Normal (⌘ sort)

module _ {A : Totalorder⍮Dec 𝑖} {V : Monoid 𝑖} where
  instance
    INotation:Union:FinFam : INotation:Union (FinFam A V)
    INotation:Union._∪_ INotation:Union:FinFam = {!!} -- _∪-FinFam_
    INotation:Union.∅ INotation:Union:FinFam = {!!} -- []


{-


-- open TypeNotation

--------------------------------------------------------------------
-- == Definition of Finite subsets

-- module _ (A : 𝒰 𝑖) {{_ : ITotalorder⍮Dec A}} (V : 𝒰 𝑗) {{_ : IMonoid V}} where
module _ (A : Totalorder⍮Dec 𝑖) (V : Monoid 𝑖) where
  data FinFam : 𝒰 (𝑖)

  size-FinFam : FinFam -> ⟨ A ⟩ +-𝒰 Lift ⊤

  instance
    INormed:FinFam : INormed ((⌘ ⟨ A ⟩) ⊕ (⌘ Lift ⊤)) FinFam
    INormed.size INormed:FinFam = size-FinFam

  data FinFam where
    [] : FinFam
    _∷[_] : (a : ⟨ A ⟩ × ⟨ V ⟩) -> (∑ λ (S : FinFam) -> (left (fst a) < ∣ S ∣)) -> FinFam

  size-FinFam [] = right (lift tt)
  size-FinFam ((a , _) ∷[ S , p ]) = min (left a) (size-FinFam S)

--------------------------------------------------------------------
-- == Set operations of finite subsets
-- module _ {A : 𝒰 𝑖} {{_ : ITotalorder⍮Dec A}} {V : 𝒰 𝑗} {{_ : IMonoid V}} where
module _ {A : Totalorder⍮Dec 𝑖} {V : Monoid 𝑖} where

  private
    insert : (⟨ A ⟩ ×-𝒰 ⟨ V ⟩) -> FinFam A V -> FinFam A V
    insert a [] = a ∷[ [] , decide-yes ]
    insert (a , va) ((b , vb) ∷[ U , x ]) with (a ≤ b) ？ | (a ≡ b) ？
    ... | P | right Q = (b , va ⋅ vb) ∷[ U , x ]
    ... | left P | left Q = (a , va) ∷[ (b , vb) ∷[ U , x ] , ({!!} , {!!}) ]
    ... | right P | left Q = (b , vb) ∷[ insert (a , va) U , {!!} ]

  _∪-FinFam_ : FinFam A V -> FinFam A V -> FinFam A V
  [] ∪-FinFam w = w
  (a ∷[ v , _ ]) ∪-FinFam w = insert a (v ∪-FinFam w)

  instance
    INotation:Union:FinFam : INotation:Union (FinFam A V)
    INotation:Union._∪_ INotation:Union:FinFam = _∪-FinFam_
    INotation:Union.∅ INotation:Union:FinFam = []



--------------------------------------------------------------------
-- Functoriality on contained items
module _ {A : Totalorder⍮Dec 𝑖} {B : Totalorder⍮Dec 𝑖} {V : Monoid 𝑖} {W : Monoid 𝑖} where

  map-FinFam : (⟨ A ⟩ -> ⟨ B ⟩) -> (MonoidHom V W) -> FinFam A V -> FinFam B W
  map-FinFam f g [] = []
  map-FinFam f g ((a , va) ∷[ x , P ]) = (f a , ⟨ g ⟩ va) ∷[ map-FinFam f g x , {!!} ]


module _ {A : Totalorder⍮Dec 𝑖} where
  instance
    IFunctor:FinFam : IFunctor (⌘ Monoid 𝑖) (⌘ 𝒰 (𝑖)) (FinFam A)
    IFunctor.map IFunctor:FinFam = map-FinFam id
    IFunctor.map/id IFunctor:FinFam = {!!}
    IFunctor.map/comp IFunctor:FinFam = {!!}


-}
