
{-# OPTIONS --cubical --no-import-sorts #-}

module Verification.Conventions.Proprelude.Imports where

open import Agda.Primitive public using (lzero)
  renaming
  (Level to 𝔏; lsuc to _⁺ ; Setω to 𝒰ω ; Set to 𝒰' ; Prop to CompProp ; _⊔_ to join-𝔏 ;
  SSet to S𝒰
  )

-- open import Cubical.Data.Empty.Base renaming (⊥ to 𝟘-𝒰 ; rec to 𝟘-rec ; elim to 𝟘-elim) public
-- open import Cubical.Data.Unit.Base renaming (Unit to 𝟙-𝒰) public
-- open import Cubical.Data.Unit.Base renaming (Unit to 𝟙-𝒰 ; isSetUnit to isSet𝟙) public

open import Verification.Conventions.Proprelude.CubicalConventions

open import Verification.Conventions.Proprelude.Replacement.Sum renaming (_⊎_ to _+-𝒰_ ; elim to elim-+-𝒰 ; inl to left ; inr to right ) hiding (map ; rec) public

-- open import Verification.Conventions.Proprelude.Replacement.Unit renaming (Unit to 𝟙-𝒰 ; isSetUnit to isSet𝟙) public

-- open import Verification.Conventions.Proprelude.Replacement.Empty renaming (⊥ to 𝟘-𝒰 ; rec to 𝟘-rec ; elim to 𝟘-elim) public

-- open import Verification.Conventions.Proprelude.Replacement.Nat renaming (_+_ to _+-ℕ_ ; _*_ to _*-ℕ_) public

-- open import Cubical.Data.Nat.Order using (Trichotomy ; lt ; eq ; gt) renaming (_≤_ to _≤-ℕ_ ; _<_ to _<-ℕ_ ; _≟_ to _≟-ℕ_ ; ≤-refl to refl-≤-ℕ ; ≤-trans to trans-≤-ℕ ; ≤-antisym to antisym-≤-ℕ) public

-- open import Cubical.Data.List hiding ([_]) renaming (_++_ to _++-List_ ; length to length-List ; ++-assoc to ++-List-assoc ; ¬cons≡nil to cons≢nil ; ¬nil≡cons to nil≢cons) public

-- open import Cubical.Data.FinData.Base renaming (Fin to Fin-R ; toℕ to toℕ-Fin-R ; ¬Fin0 to ¬Fin0-R) public

-- open import Cubical.Data.Bool.Base renaming (_≟_ to _≟-Bool_ ; _⊕_ to _⊕-Bool_) public
-- open import Cubical.Data.Bool.Properties public

open import Verification.Conventions.Proprelude.Replacement.Path public

open import Agda.Builtin.String public



-- these
open import Agda.Builtin.Sigma public
open import Agda.Builtin.Bool public


--------------------------------------------------------------------------------
-- other predefineds:



--------------------------------------------------------------------------------
-- copy the lifting
record Lift {i j} (A : 𝒰' i) : 𝒰' (join-𝔏 i j) where
  constructor lift
  field
    lower : A

open Lift public





