
module Verification.Core.Theory.Computation.Problem.Specific.Parsing where

open import Verification.Core.Conventions
open import Verification.Core.Theory.Formal.Presentation.Signature.SingleSorted.Definition

-- data Term-位 : 饾挵鈧? where
--   app : (f g : Term-位) -> Term-位
--   lam : (t : Term-位) -> Term-位
--   var : 鈩? -> Term-位
--   par : Term-位 -> Term-位

data TeSig : 鈩? -> 饾挵鈧? where
  `var` : String -> TeSig 0
  `lam` : String -> TeSig 1
  `app` : TeSig 2
  `par` : TeSig 1

Term-位 = Term {鈩撯個} TeSig

-- data Tok-位 : 


-- data TokKind : 饾挵鈧? where
--   varK symK : TokKind

-- Tokens : 饾挵鈧?
-- Tokens = List (String 脳-饾挵 TokKind)

-- 蟺-Term : Term-位 -> Tokens
-- 蟺-Term = {!!}



