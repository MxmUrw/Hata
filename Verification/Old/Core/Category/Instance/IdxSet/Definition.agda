
module Verification.Old.Core.Category.Instance.IdxSet.Definition where

open import Verification.Conventions
open import Verification.Old.Core.Category.Definition
open import Verification.Old.Core.Category.Proper
open import Verification.Old.Core.Homotopy.Level
open import Verification.Old.Core.Category.Instance.Type


record IIdxSet (K : ๐ฐ ๐) {๐} (A : K -> ๐ฐ ๐) : ๐ฐ (๐ ๏ฝค ๐) where
  field {{ISet:this}} : โ{k : K} -> ISet (A k)
open IIdxSet {{...}} public
unquoteDecl IdxSet idxSet = #struct "IdxSt" (quote IIdxSet) "A" IdxSet idxSet

record IIdxSetHom {K : ๐ฐ ๐} (A : IdxSet K ๐) (B : IdxSet K ๐) (f : โ{k : K} -> โจ A โฉ k -> โจ B โฉ k) : ๐ฐ (๐ ๏ฝค ๐) where

instance
  IIdxSetHom:Anything : {K : ๐ฐ ๐} {A : IdxSet K ๐} {B : IdxSet K ๐} {f : โ{k : K} -> โจ A โฉ k -> โจ B โฉ k} -> IIdxSetHom A B f
  IIdxSetHom:Anything = record {}

open IIdxSetHom {{...}} public
unquoteDecl IdxSetHom idxSetHom = #struct "IdxStHom" (quote IIdxSetHom) "f" IdxSetHom idxSetHom

module _ {K : ๐ฐ ๐} where
  record is-โฃ-IdxSet {A : IdxSet K ๐} {B : IdxSet K ๐} (f g : IdxSetHom A B) (P : โ{k} x -> โจ f โฉ {k} x โก โจ g โฉ {k} x) : ๐ฐ (๐ ๏ฝค ๐) where

  instance
    is-โฃ-IdxSet-Anything : {A : IdxSet K ๐} {B : IdxSet K ๐} {f g : IdxSetHom A B} {P : โ{k} x -> โจ f โฉ {k} x โก โจ g โฉ {k} x} -> is-โฃ-IdxSet f g P
    is-โฃ-IdxSet-Anything = record {}


open is-โฃ-IdxSet {{...}} public
unquoteDecl _โฃ-IdxSet_ mk-โฃ-IdxSet = #struct "_โฃ_" (quote is-โฃ-IdxSet) "P" _โฃ-IdxSet_ mk-โฃ-IdxSet

module _ {K : ๐ฐ ๐} where
  instance
    isEquivRel:โฃ-IdxSet : {A : IdxSet K ๐} {B : IdxSet K ๐} -> isEquivRel (_โฃ-IdxSet_ {A = A} {B = B})
    โจ isEquivRel.refl isEquivRel:โฃ-IdxSet โฉ _ = refl
    โจ isEquivRel.sym isEquivRel:โฃ-IdxSet p โฉ x = โจ p โฉ x โปยน
    โจ isEquivRel._โ_ isEquivRel:โฃ-IdxSet p q โฉ x = โจ p โฉ x โ โจ q โฉ x

instance
  isEquivRel:โฃ-on-IdxSet : {K : ๐ฐ ๐} {A : IdxSet K ๐} {B : IdxSet K ๐} -> isEquivRel (ฮป (f g : IdxSetHom A B) -> โ{k} -> โ x -> โจ f โฉ {k} x โก โจ g โฉ {k} x)
  isEquivRel.refl isEquivRel:โฃ-on-IdxSet x = refl
  isEquivRel.sym isEquivRel:โฃ-on-IdxSet p xโ = p _ โปยน
  isEquivRel._โ_ isEquivRel:โฃ-on-IdxSet p q _ = p _ โ q _



Category:IdxSet : โ(K : ๐ฐ ๐) -> โ ๐ -> Category (๐ โบ โ ๐ , (๐ โ ๐) , (๐ โ ๐))
โจ Category:IdxSet K ๐ โฉ = IdxSet K ๐
isCategory.Hom (of Category:IdxSet K ๐) = IdxSetHom
isCategory._โฃ_ (of Category:IdxSet K ๐) f g = โ{k} -> โ x -> โจ f โฉ {k} x โก โจ g โฉ {k} x
-- f โฃ-IdxSet g -- 
-- โ {k} x -> โจ f โฉ {k} x โก โจ g โฉ {k} x
isCategory.isEquivRel:โฃ (of Category:IdxSet K ๐) = isEquivRel:โฃ-on-IdxSet
isCategory.id (of Category:IdxSet K ๐) = idxSetHom (id)
isCategory._โ_ (of Category:IdxSet K ๐) f g = ` (ฮป {k} -> โจ f โฉ {k} โ โจ g โฉ {k}) `
isCategory.unit-l-โ (of Category:IdxSet K ๐) = {!!}
isCategory.unit-r-โ (of Category:IdxSet K ๐) = {!!}
isCategory.unit-2-โ (of Category:IdxSet K ๐) = {!!}
isCategory.assoc-l-โ (of Category:IdxSet K ๐) = {!!}
isCategory.assoc-r-โ (of Category:IdxSet K ๐) = {!!}
isCategory._โ_ (of Category:IdxSet K ๐) = {!!}

instance isCategory:IdxSet = #openstruct Category:IdxSet

module _ {K : ๐ฐ ๐} where
  instance
    I1Category:IdxSet : I1Category (Category:IdxSet K ๐)
    I1Category:IdxSet = {!!}


