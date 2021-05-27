

module Verification.Core.Category.Monad.Definition where

open import Verification.Conventions
open import Verification.Core.Category.Definition
open import Verification.Core.Category.Instance.Type
open import Verification.Core.Category.Instance.Cat

--------------------------------------------------------------------
-- == Monads

-- In this section we define monads.
-- | Let [..] be a category.
module _ {𝒞 : Category 𝑖} where
-- [Definition]
-- | A functor |F : 𝒞 ⟶ 𝒞| is a monad,
  record IMonad (F : 𝒞 ⟶ 𝒞) : 𝒰 (⨆ 𝑖) where
-- | if the following additional data is given:

-- | - Two maps |return| and |join|:
    field return  : ∀{A} -> A ⟶ (⟨ F ⟩ A)
          join    : ∀{A} -> (⟨ F ◆ F ⟩ A) ⟶ (⟨ F ⟩ A)
-- | - Proofs that they are natural:
          {{INatural:return}}  : INatural id (F) return
          {{INatural:join}}    : INatural (F ◆ F) (F) join
-- | - And behave monoidal.
          unit-l-join  : ∀{A : ⟨ 𝒞 ⟩} -> return ◆ join ≣ id {a = ⟨ F ⟩ A}
          unit-r-join  : ∀{A : ⟨ 𝒞 ⟩} -> map return ◆ join ≣ id {a = ⟨ F ⟩ A}
          assoc-join   : ∀{A : ⟨ 𝒞 ⟩} -> join ◆ join ≣ (map join) ◆ join {A = A}
  open IMonad {{...}} public
-- //

unquoteDecl Monad monad = #struct "Mnd" (quote IMonad) "F" Monad monad

-- #Notation/Annotatable# return
-- #Notation/Annotatable# join


-- [Hide]
-- | We define a shorthand for monads on \AD{𝒰 𝑖}
ISetMonad : (F : Functor (′ 𝒰 𝑖 ′) (′ 𝒰 𝑖 ′)) -> 𝒰 (𝑖 ⁺)
ISetMonad F = IMonad F

module _ {𝒞 : Category 𝑖} {F : Functor 𝒞 𝒞} {{_ : IMonad F}} where
-- | And some common notation which may be used.
  module MonadNotation where
    -- η : ∀{𝒞 : 𝒰 (𝑖 ⁺)} {{_ : ICategory 𝒞 𝑖𝑖}} {F : 𝒞 -> 𝒞} {{_ : IMonad F}} -> ∀{A} -> Hom A (F A)
    η : ∀{A} -> Hom A (⟨ F ⟩ A)
    η = return

    -- μ : ∀{𝒞 : 𝒰 (𝑖 ⁺)} {{_ : ICategory 𝒞 𝑖𝑖}} {F : 𝒞 -> 𝒞} {{_ : IMonad F}} -> ∀{A} -> Hom (F (F A)) (F A)
    μ : ∀{A} -> Hom (⟨ F ⟩ (⟨ F ⟩ A)) (⟨ F ⟩ A)
    μ = join

-- | The Kleisli fish, i.e., composition is:
  _>=>_ : ∀{A B C : ⟨ 𝒞 ⟩} -> (f : Hom A (⟨ F ⟩ B)) -> (g : Hom B (⟨ F ⟩ C)) -> Hom A (⟨ F ⟩ C)
  f >=> g = (f ◆ map g) ◆ join

  _=<< : ∀{A B : ⟨ 𝒞 ⟩} -> (A ⟶ ⟨ F ⟩ B) -> (⟨ F ⟩ A ⟶ ⟨ F ⟩ B)
  f =<< = map f ◆ join


module _ {F : Functor (′ 𝒰 𝑖 ′) (′ 𝒰 𝑖 ′)} {{_ : IMonad F}} where
  _>>=_ : ∀{A B} -> ⟨ F ⟩ A -> (A -> ⟨ F ⟩ B) -> ⟨ F ⟩ B
  a >>= f = join (map f a)

  _*>_ : ∀{A B} -> ⟨ F ⟩ A -> (⟨ F ⟩ B) -> ⟨ F ⟩ B
  a *> f = a >>= (λ _ -> f)

  _<*_ : ∀{A B} -> ⟨ F ⟩ B -> (⟨ F ⟩ A) -> ⟨ F ⟩ B
  a <* f = a >>= (λ x -> f *> return x)

  _>>_ : ∀{A B} -> ⟨ F ⟩ A -> (⟨ F ⟩ B) -> ⟨ F ⟩ B
  a >> f = a *> f

  >>=/return : ∀{A B} -> (a : A) -> (f : A -> ⟨ F ⟩ B) -> return a >>= f ≡ f a
  >>=/return a f = return a >>= f ≡⟨ refl ⟩
                  join (map f (return a)) ≡[ i ]⟨ join (naturality f i a) ⟩
                  join (return (f a)) ≡[ i ]⟨ unit-l-join i (f a) ⟩
                  f a ∎

-- //

--- >>=/return-inside : ∀{F : 𝒰₀ -> 𝒰₀} {{_ : IMonad F}} -> ∀{A B : 𝒰₀} -> (a : F A) -> (f : A -> B) -> a >>= (λ x -> return (f x)) ≡ return (f a)
--- >>=/return-inside = ?

  -- comp-Kleisli : ∀{F : 𝒰 𝑖 -> 𝒰 𝑖} {{_ : ISetMonad F}} -> ∀{A B C : 𝒰 𝑖} -> (A -> F B) -> (B -> F C) -> A -> F C
  -- comp-Kleisli f g a = f a >>= g




-- ICategory:Kleisli : ∀{F : Functor (⌘ 𝒰 𝑖) (⌘ 𝒰 𝑖)} {{_ : IMonad F}} -> ICategory (𝒰 𝑖) (𝑖 , 𝑖)
-- ICategory:Kleisli = {!!}


-- Hom (ICategory:Kleisli {F = F}) A B = A -> ⟨ F ⟩ B
-- _≣_ (ICategory:Kleisli) = _≡_
-- IEquiv:≣ (ICategory:Kleisli) = IEquiv:Path
-- id (ICategory:Kleisli) = return
-- _◆_ (ICategory:Kleisli) = _>=>_
-- _◈_ (ICategory:Kleisli) = {!!}
-- /id◆  ICategory:Kleisli = {!!}
-- /◆id  ICategory:Kleisli = {!!}
-- /id₂  ICategory:Kleisli = {!!}
-- /◆◆ₗ  ICategory:Kleisli = {!!}
-- /◆◆ᵣ  ICategory:Kleisli = {!!}



