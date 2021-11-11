

module Verification.Conventions.Prelude.Data.List where

open import Verification.Conventions.Proprelude
open import Verification.Conventions.Prelude.Classes
open import Verification.Conventions.Prelude.Data.String
open import Verification.Conventions.Prelude.Data.Nat
open import Verification.Conventions.Prelude.Data.Bool

open import Verification.Conventions.Prelude.Data.List.Base hiding ([_]) renaming (_++_ to _++-List_ ; length to length-List) public
-- open import Verification.Conventions.Prelude.Data.List.Properties renaming (++-assoc to ++-List-assoc ; ¬cons≡nil to cons≢nil ; ¬nil≡cons to nil≢cons) public



instance
  IShow:List : ∀{A : 𝒰 𝑖} {{_ : IShow A}} -> IShow (List A)
  IShow.show (IShow:List {A = A}) = f
    where f : List A -> String
          f [] = ""
          f (x ∷ xs) with show x
          ... | "" = f xs
          ... | t = t <> " " <> f xs


  IBootMonoid:List : ∀{A : 𝒰 𝑖} -> IBootMonoid (List A)
  IBootMonoid.mempty IBootMonoid:List = []
  IBootMonoid._<>_ IBootMonoid:List = _++-List_

  IBootEq:List : ∀{A : 𝒰 𝑖} -> {{_  : IBootEq A}} -> IBootEq (List A)
  IBootEq._≟_ IBootEq:List = f
    where
      f : ∀{A : 𝒰 𝑖} -> {{_  : IBootEq A}} -> (List A) -> List A -> Bool
      f [] [] = true
      f [] (x ∷ ys) = false
      f (x ∷ xs) [] = false
      f (x ∷ xs) (y ∷ ys) = (x ≟ y) and (f xs ys)


module _ {A : 𝒰 𝑖} {{_ : IBootEq A}} where
  _∈?-List_ :  (a : A) -> (xs : List A) -> Bool
  a ∈?-List xs = foldr (λ a' res -> (a' ≟ a) or res) false xs

module _ {A : 𝒰 𝑖} where
  filter : (A -> Bool) -> List A -> List A
  filter f [] = []
  filter f (x ∷ xs) with f x
  ... | true = x ∷ filter f xs
  ... | false = filter f xs

module _ {A : 𝒰 𝑖} where
  skip-List : ℕ -> List A -> List A
  skip-List zero xs = xs
  skip-List (suc n) [] = []
  skip-List (suc n) (x ∷ xs) = skip-List n xs


map-List : ∀{A : 𝒰 𝑖} {B : 𝒰 𝑗} -> (A -> B) -> List A -> List B
map-List f [] = []
map-List f (x ∷ xs) = f x ∷ map-List f xs
