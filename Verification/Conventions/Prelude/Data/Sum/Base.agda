
--
-- NOTE: This file is originally from the cubical std library.
--       (https://github.com/agda/cubical)
--       It was copied here to replace references to cubical paths,
--       since cubical agda files cannot currently be compiled to binaries.
--       All copyright belongs to the original authors.
--
-- See:
-- module Cubical.Data.Sum.Base where
--

module Verification.Conventions.Prelude.Data.Sum.Base where

open import Verification.Conventions.Proprelude.Init
open import Cubical.Core.Everything

private
  variable
    ℓ ℓ' : Level
    A B C D : Type ℓ

-- data _+-𝒰_ (A : Type ℓ)(B : Type ℓ') : Type (ℓ-max ℓ ℓ') where
--   left : A → A +-𝒰 B
--   right : B → A +-𝒰 B

rec : {C : Type ℓ} → (A → C) → (B → C) → A +-𝒰 B → C
rec f _ (left x) = f x
rec _ g (right y) = g y

elim : {C : A +-𝒰 B → Type ℓ} →  ((a : A) → C (left a)) → ((b : B) → C (right b))
       → (x : A +-𝒰 B) → C x
elim f _ (left x) = f x
elim _ g (right y) = g y

map : (A → C) → (B → D) → A +-𝒰 B → C +-𝒰 D
map f _ (left x) = left (f x)
map _ g (right y) = right (g y)

-- _+-𝒰?_ : {P Q : Type ℓ} → Dec P → Dec Q → Dec (P +-𝒰 Q)
-- P? +-𝒰? Q? with P? | Q?
-- ... | yes p | _ = yes (left p)
-- ... | no _  | yes q = yes (right q)
-- ... | no ¬p | no ¬q  = no λ
--   { (left p) → ¬p p
--   ; (right q) → ¬q q
--   }
