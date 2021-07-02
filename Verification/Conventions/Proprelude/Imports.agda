
-- {-# OPTIONS --cubical --no-import-sorts #-}

module Verification.Conventions.Proprelude.Imports where

open import Agda.Primitive public using (lzero)
  renaming
  (Level to 𝔏; lsuc to _⁺ ; Setω to 𝒰ω ; Set to 𝒰' ; Prop to CompProp ; _⊔_ to join-𝔏 ;
  SSet to S𝒰
  )


open import Agda.Builtin.String public

-- open import Verification.VHM2.Conventions.Base hiding (_==_ ; tail ; _∎ ; _∙_ ; cong) public
open import Cubical.Core.Everything hiding (Type ; _∧_ ; _∨_ ; isEquiv)
  public

open import Cubical.Foundations.Prelude
  hiding (Type)
  renaming (refl to refl-Path ; sym to sym-Path ; _∙_ to trans-Path ; _∎ to _∎-Path ;
            cong₂ to cong₂-Path ;
            _∧_ to _⋏_ ; _∨_ to _⋎_)
  public
-- open import Cubical.Relation.Nullary public using (¬_) -- renaming (Dec to Decision) hiding (∣_∣)
open import Cubical.Foundations.HLevels public
open import Cubical.Foundations.GroupoidLaws public renaming (assoc to assoc-Path ; _⁻¹ to _⁻¹-Grpd)
open import Cubical.Foundations.Id using (Id ; idToPath) renaming (refl to refl-Id ; J to J-Id ; _≡_ to _≡!_ ; _⁻¹ to sym-Id ; transport to transport-Id ; ap to cong-Id) public
-- open import Cubical.Foundations.Isomorphism public renaming (Iso to Iso-𝒰 ; iso to iso-𝒰)


open import Cubical.HITs.SetTruncation renaming (elim to ∥_∥₂-elim ; elim2 to ∥_∥₂-elim2 ; elim3 to ∥_∥₂-elim3 ; rec to ∥_∥₂-rec ; map to map-∥₂) public
open import Cubical.HITs.PropositionalTruncation renaming (∣_∣ to ∣_∣-Prop ; elim to ∥_∥₁-elim ; elim2 to ∥_∥₁-elim2 ; elim3 to ∥_∥₁-elim3 ; rec to ∥_∥₁-rec ; rec2 to rec2-∥₁ ; map to map-∥₁) public

-- open import Cubical.Data.Empty renaming (⊥ to 𝟘-𝒰 ; rec to 𝟘-rec ; elim to 𝟘-elim) public
-- open import Cubical.Data.Unit renaming (Unit to 𝟙-𝒰 ; isSetUnit to isSet𝟙) public
-- open import Cubical.Data.FinData.Base renaming (Fin to Fin-R ; toℕ to toℕ-Fin-R ; ¬Fin0 to ¬Fin0-R) public
open import Cubical.Data.Fin.Base renaming (elim to elim-Fin ; toℕ to toℕ-Fin) public
-- open import Cubical.Data.Bool.Base renaming (_≟_ to _≟-Bool_ ; _⊕_ to _⊕-Bool_) public
-- open import Cubical.Data.Bool.Properties public
open import Cubical.Data.Vec.Properties public
open import Cubical.Data.Vec.Base renaming (map to map-Vec ; _++_ to _++-Vec_ ; length to length-Vec) public
-- open import Cubical.Data.List hiding ([_]) renaming (_++_ to _++-List_ ; length to length-List ; ++-assoc to ++-List-assoc ; ¬cons≡nil to cons≢nil ; ¬nil≡cons to nil≢cons) public


---------------------------
-- importing Nats

-- ** these are the original cubical files **

-- open import Cubical.Data.Nat.Base renaming (_+_ to _+-ℕ_ ; _*_ to _*-ℕ_) public
-- open import Cubical.Data.Nat.Properties renaming (znots to zero≢suc ; snotz to suc≢zero ; +-assoc to assoc-+-ℕ ; +-comm to comm-+-ℕ) public
-- open import Cubical.Data.Nat.Order renaming (_≤_ to _≤-ℕ_ ; _<_ to _<-ℕ_ ; _≟_ to _≟-ℕ_ ; ≤-refl to refl-≤-ℕ ; ≤-trans to trans-≤-ℕ ; ≤-antisym to antisym-≤-ℕ) public


-- open import Cubical.Data.Int renaming (Int to ℤ ; _+_ to _+-ℤ_ ; _-_ to _-ℤ_ ; +-assoc to assoc-+-ℤ ; +-comm to comm-+-ℤ) public
-- open import Cubical.Data.Sum renaming (_⊎_ to _+-𝒰_ ; elim to elim-+-𝒰 ; inl to left ; inr to right ) hiding (map ; rec) public


open import Cubical.Induction.WellFounded hiding (Rel) public
