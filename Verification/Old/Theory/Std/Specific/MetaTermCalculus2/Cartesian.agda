
module Verification.Core.Theory.Std.Specific.MetaTermCalculus2.Cartesian where

open import Verification.Core.Conventions hiding (Structure)
open import Verification.Core.Algebra.Monoid.Definition
open import Verification.Core.Algebra.Monoid.Free
open import Verification.Core.Order.Lattice
open import Verification.Core.Data.Universe.Definition
open import Verification.Core.Data.Universe.Instance.Category
open import Verification.Core.Data.Product.Definition
open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Theory.Std.Generic.TypeTheory.Definition
open import Verification.Core.Theory.Std.Generic.TypeTheory.Simple
open import Verification.Core.Theory.Std.Generic.TypeTheory.Simple.Judgement2
open import Verification.Core.Theory.Std.TypologicalTypeTheory.CwJ.Definition
open import Verification.Core.Category.Std.Category.Structured.Monoidal.Definition
open import Verification.Core.Category.Std.Functor.Definition
open import Verification.Core.Theory.Std.Generic.TypeTheory.Simple

module _ {K : ๐ฐ ๐} (R : List K -> K -> ๐ฐ ๐) where
  data Subs : (ฮ : (List K)) -> (ฮ : List K) -> ๐ฐ (๐ ๏ฝค ๐) where
    [] : โ{ฮ} -> Subs ฮ []
    _โท_ : โ{ฮ ฮ k} -> R ฮ k -> Subs ฮ ฮ -> Subs ฮ (k โท ฮ)

module _ {K : ๐ฐ ๐} {R : List K -> K -> ๐ฐ ๐} where
  getvar : โ{ฮ ฮ k} -> Subs R ฮ ฮ -> ฮ โจ-var k -> R ฮ k
  getvar (x โท s) zero = x
  getvar (x โท s) (suc i) = getvar s i


record Jdgโ (A : ๐ฐ ๐) : ๐ฐ ๐ where
  constructor _โฃ_โ_
  field fst : List A
  field snd : List (Jdg A)
  field thd : Jdg A
infix 4 _โฃ_โ_

record MetaTermCalculus (K : Kinding ๐) (๐ : ๐): ๐ฐ (๐ โบ ๏ฝค ๐ โบ) where
  field TermCon : (ฯ : List (Jdg โจ K โฉ)) -> Jdg โจ K โฉ -> ๐ฐ (๐)

open MetaTermCalculus public

module MTCDefinitions {K : Kinding ๐} (ฮณ : MetaTermCalculus K ๐) where


  data _โฉแถ โ_ : (๐s : List (Jdgโ โจ K โฉ)) -> Jdgโ โจ K โฉ -> ๐ฐ (๐ ๏ฝค ๐) where
    meta : โ{๐ ฮ ฮ ฮฑ} -> ๐ โจ-var (ฮ โฃ ฮ โ ฮฑ) -> ๐ โฉแถ โ (ฮ โฃ ฮ โ ฮฑ)
    lam  : โ{๐ ฮ ฮ ฮฑ ฮฑs ฮฒ} -> (t : ๐ โฉแถ โ (ฮ โฃ [] โ ([] โข โโ ฮฑ)))
                            -> (s : ๐ โฉแถ โ ((ฮฑ โท ฮ) โฃ ฮ โ (ฮฑs โข ฮฒ)))
                            -> ๐ โฉแถ โ (ฮ โฃ ฮ โ ((ฮฑ โท ฮฑs) โข ฮฒ))
    app  : โ{๐ ฮ ฮ ๐ง ฮฒ}
          -> (t : ๐ โฉแถ โ (ฮ โฃ (๐ง โท ฮ) โ ฮฒ)) -> (s : ๐ โฉแถ โ (ฮ โฃ [] โ ๐ง))
          -> ๐ โฉแถ โ (ฮ โฃ ฮ โ ฮฒ)

    con : โ{๐ ฮ ฮ ฮฑ} -> TermCon ฮณ ฮ ฮฑ -> ๐ โฉแถ โ (ฮ โฃ ฮ โ ฮฑ)

    var : โ{๐ ฮ ฮฑ} -> ฮ โจ-var ฮฑ -> ๐ โฉแถ โ (ฮ โฃ [] โ ([] โข ฮฑ))



