{-# OPTIONS --cubical --allow-unsolved-metas #-}

module Verification.Conventions.Prelude.Data.Int where

open import Verification.Conventions.Prelude.Data.Int.Base public
open import Verification.Conventions.Prelude.Data.Int.Properties renaming (_+_ to _+-ℤ_ ; _-_ to _-ℤ_ ; +-assoc to assoc-+-ℤ ; +-comm to comm-+-ℤ) public

-- open import Cubical.Data.Int renaming (Int to ℤ ; _+_ to _+-ℤ_ ; _-_ to _-ℤ_ ; +-assoc to assoc-+-ℤ ; +-comm to comm-+-ℤ) public

