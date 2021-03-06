
{-# OPTIONS --cubical --allow-unsolved-metas #-}

module Verification.Old.Core.Category.Iso where

open import Verification.Conventions
open import Verification.Old.Core.Category.Definition
-- open import Verification.Old.Core.Category.Instance.Cat
open import Verification.Old.Core.Category.Instance.Type.Definition

module _ {X : ๐ฐ ๐} {{_ : isCategory X ๐}} where

  record IIso (a b : X) (f : a โถ b) : ๐ฐ (๐ โ 0 โ ๐ โ 1) where
    field inverse : b โถ a
          /โฒ : f โ inverse โฃ id
          /โณ : inverse โ f โฃ id

unquoteDecl _โ_ iso = #struct "Iso" (quote IIso) "f" _โ_ iso
open IIso public

module _ {X : Category ๐} {a b : โจ X โฉ} where
  -- instance
    Notation-Inverse:Iso : Notation-Inverse (a โ b) (b โ a)
    โจ (Notation-Inverse:Iso Notation-Inverse.โปยน) x โฉ = inverse (of x)
    IIso.inverse (of ((Notation-Inverse:Iso Notation-Inverse.โปยน) x)) = โจ x โฉ
    IIso./โฒ (of ((Notation-Inverse:Iso Notation-Inverse.โปยน) x)) = /โณ (of x)
    IIso./โณ (of ((Notation-Inverse:Iso Notation-Inverse.โปยน) x)) = /โฒ (of x)

infixl 50 _โ-๐ฐ_
_โ-๐ฐ_ = comp-๐ฐ

record IIso-๐ฐ (a : ๐ฐ ๐) (b : ๐ฐ ๐) (f : a -> b) : ๐ฐ (๐ ๏ฝค ๐) where
  field inverse-๐ฐ : b -> a
        /โฒ-๐ฐ : f โ-๐ฐ inverse-๐ฐ โก id
        /โณ-๐ฐ : inverse-๐ฐ โ-๐ฐ f โก id
open IIso-๐ฐ {{...}} public
unquoteDecl _โ-๐ฐ_ iso-๐ฐ = #struct "TyIso" (quote IIso-๐ฐ) "f" _โ-๐ฐ_ iso-๐ฐ

module _ {a : ๐ฐ ๐} {b : ๐ฐ ๐} where
  instance
    Notation-Inverse:Iso-๐ฐ : Notation-Inverse (a โ-๐ฐ b) (b โ-๐ฐ a)
    โจ (Notation-Inverse:Iso-๐ฐ Notation-Inverse.โปยน) x โฉ = inverse-๐ฐ
    IIso-๐ฐ.inverse-๐ฐ (of ((Notation-Inverse:Iso-๐ฐ Notation-Inverse.โปยน) x)) = โจ x โฉ
    IIso-๐ฐ./โฒ-๐ฐ (of ((Notation-Inverse:Iso-๐ฐ Notation-Inverse.โปยน) x)) = /โณ-๐ฐ
    IIso-๐ฐ./โณ-๐ฐ (of ((Notation-Inverse:Iso-๐ฐ Notation-Inverse.โปยน) x)) = /โฒ-๐ฐ


-- record Abstract (A : ๐ฐ ๐) (B : ๐ฐ ๐) : ๐ฐ (๐ ๏ฝค ๐) where
--   field abstraction : A โ-๐ฐ B
--   abst : A -> B
--   abst = โจ abstraction โฉ
--   conc : B -> A
--   conc = โจ abstraction โปยน โฉ
-- open Abstract {{...}} public


record ILiftHom {X : ๐ฐ ๐} {{_ : isCategory X ๐}} (a b : X) (A : ๐ฐ ๐) : ๐ฐ (๐ ๏ฝค ๐ ๏ฝค ๐) where
  field liftHom : A โ-๐ฐ (Hom a b)
open ILiftHom {{...}} public


