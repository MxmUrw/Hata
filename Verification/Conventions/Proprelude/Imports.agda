
-- {-# OPTIONS --cubical --no-import-sorts #-}

module Verification.Conventions.Proprelude.Imports where

open import Agda.Primitive public using (lzero)
  renaming
  (Level to π; lsuc to _βΊ ; SetΟ to π°Ο ; Set to π°' ; Prop to CompProp ; _β_ to join-π ;
  SSet to Sπ°
  )


open import Agda.Builtin.String public
  renaming (String to Text)

String = Text



-- open import Verification.VHM2.Conventions.Base hiding (_==_ ; tail ; _β ; _β_ ; cong) public
-- open import Cubical.Core.Everything hiding (Type ; _β§_ ; _β¨_ ; isEquiv)
--   public

open import Cubical.Foundations.Prelude
  hiding (Type ; Lift ; lift ; lower ; isGroupoid)
  renaming (refl to refl-Path ; sym to sym-Path ; _β_ to trans-Path ; _β to _β-Path ;
            congβ to congβ-Path ;
            _β§_ to _β_ ; _β¨_ to _β_)
  public
-- open import Cubical.Relation.Nullary public using (Β¬_) -- renaming (Dec to Decision) hiding (β£_β£)
-- open import Cubical.Foundations.HLevels public
-- open import Cubical.Foundations.GroupoidLaws public renaming (assoc to assoc-Path ; _β»ΒΉ to _β»ΒΉ-Grpd)
-- open import Cubical.Foundations.Id using (Id ; idToPath) renaming (refl to refl-Id ; J to J-Id ; _β‘_ to _β‘!_ ; _β»ΒΉ to sym-Id ; transport to transport-Id ; ap to cong-Id) public
-- open import Cubical.Foundations.Isomorphism public renaming (Iso to Iso-π° ; iso to iso-π°)


-- open import Cubical.HITs.SetTruncation renaming (elim to β₯_β₯β-elim ; elim2 to β₯_β₯β-elim2 ; elim3 to β₯_β₯β-elim3 ; rec to β₯_β₯β-rec ; map to map-β₯β) public
-- open import Cubical.HITs.PropositionalTruncation renaming (β£_β£ to β£_β£-Prop ; elim to β₯_β₯β-elim ; elim2 to β₯_β₯β-elim2 ; elim3 to β₯_β₯β-elim3 ; rec to β₯_β₯β-rec ; rec2 to rec2-β₯β ; map to map-β₯β) public

-- open import Cubical.Data.Empty renaming (β₯ to π-π° ; rec to π-rec ; elim to π-elim) public
-- open import Cubical.Data.Unit renaming (Unit to π-π° ; isSetUnit to isSetπ) public
-- open import Cubical.Data.FinData.Base renaming (Fin to Fin-R ; toβ to toβ-Fin-R ; Β¬Fin0 to Β¬Fin0-R) public
-- open import Cubical.Data.Fin.Base renaming (elim to elim-Fin ; toβ to toβ-Fin) public
-- open import Cubical.Data.Bool.Base renaming (_β_ to _β-Bool_ ; _β_ to _β-Bool_) public
-- open import Cubical.Data.Bool.Properties public
-- open import Cubical.Data.Vec.Properties public
-- open import Cubical.Data.Vec.Base renaming (map to map-Vec ; _++_ to _++-Vec_ ; length to length-Vec) public
-- open import Cubical.Data.List hiding ([_]) renaming (_++_ to _++-List_ ; length to length-List ; ++-assoc to ++-List-assoc ; Β¬consβ‘nil to consβ’nil ; Β¬nilβ‘cons to nilβ’cons) public


---------------------------
-- importing Nats

-- ** these are the original cubical files **

-- open import Cubical.Data.Nat.Base renaming (_+_ to _+-β_ ; _*_ to _*-β_) public
-- open import Cubical.Data.Nat.Properties renaming (znots to zeroβ’suc ; snotz to sucβ’zero ; +-assoc to assoc-+-β ; +-comm to comm-+-β) public
-- open import Cubical.Data.Nat.Order renaming (_β€_ to _β€-β_ ; _<_ to _<-β_ ; _β_ to _β-β_ ; β€-refl to refl-β€-β ; β€-trans to trans-β€-β ; β€-antisym to antisym-β€-β) public


-- open import Cubical.Data.Int renaming (Int to β€ ; _+_ to _+-β€_ ; _-_ to _-β€_ ; +-assoc to assoc-+-β€ ; +-comm to comm-+-β€) public
-- open import Cubical.Data.Sum renaming (_β_ to _+-π°_ ; elim to elim-+-π° ; inl to left ; inr to right ) hiding (map ; rec) public


-- open import Cubical.Induction.WellFounded hiding (Rel) public
