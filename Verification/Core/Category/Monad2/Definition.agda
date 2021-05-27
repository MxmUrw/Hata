
module Verification.Core.Category.Monad2.Definition where

open import Verification.Conventions
open import Verification.Core.Category.Definition
open import Verification.Core.Category.Instance.Type
open import Verification.Core.Category.Instance.Cat

--------------------------------------------------------------------
-- == Monads

-- In this section we define monads.


module _ {𝒞 : Category 𝑖} where
-- [Definition]
-- | A monad is given by:
  record IMonad (F : ⟨ 𝒞 ⟩ ⟶ ⟨ 𝒞 ⟩) {{IFunctor:this : IFunctor 𝒞 𝒞 F}} : 𝒰 (⨆ 𝑖) where
    field
          
          return  : ∀{A} -> A ⟶ (F A)
          join    : ∀{A} -> (F (F A)) ⟶ (F A)
          {{INatural:return}}  : INatural id ` F ` return
          {{INatural:join}}    : INatural (` F ` ◆ ` F `) (` F `) join
          unit-l-join  : ∀{A : ⟨ 𝒞 ⟩} -> return ◆ join ≡ id {a = F A}
          unit-r-join  : ∀{A : ⟨ 𝒞 ⟩} -> map return ◆ join ≡ id {a = F A}
          assoc-join   : ∀{A : ⟨ 𝒞 ⟩} -> join ◆ join ≡ (map join) ◆ join {A = A}
  open IMonad {{...}} public
-- //

-- unquoteDecl Monad monad = #struct "Mnd" (quote IMonad) "F" Monad monad

Monad : Category 𝑖 -> 𝒰 𝑖
Monad 𝒞 = Structure (λ (F : Functor 𝒞 𝒞) -> IMonad ⟨ F ⟩)

monad : {𝒞 : Category 𝑖} (F : ⟨ 𝒞 ⟩ ⟶ ⟨ 𝒞 ⟩) {{_  : IFunctor 𝒞 𝒞 F}} {{_ : IMonad F}} -> Monad 𝒞
monad F = ⌘ (⌘ F)

-- record IBoth {A : 𝒰 𝑖} (P : A -> 𝒰 𝑗) (Q : A -> 𝒰 𝑘) (a : A) : 𝒰 (𝑖 ､ 𝑘 ､ 𝑗) where
--   field {{Cond1}} : P a
--         {{Cond2}} : Q a

-- instance
--   Cast:Monad : {𝒞 : Category 𝑖} -> Cast (⟨ 𝒞 ⟩ ⟶ ⟨ 𝒞 ⟩) (IBoth (IFunc)) {{_ : IFunctor 𝒞 𝒞 F}} {{_ }}

-- #Notation/Annotatable# return
-- #Notation/Annotatable# join



-- | We define a shorthand for monads on \AD{𝒰 𝑖}
-- ISetMonad : (F : Functor (⌘ 𝒰 𝑖) (⌘ 𝒰 𝑖)) -> 𝒰 (𝑖 ⁺)
-- ISetMonad F = IMonad F

-- module _ {𝒞 : Category 𝑖} {F : Functor 𝒞 𝒞} {{_ : IMonad F}} where
module _ {𝒞 : Category 𝑖} {F : ⟨ 𝒞 ⟩ ⟶ ⟨ 𝒞 ⟩}{{_ : IFunctor 𝒞 𝒞 F}} {{_ : IMonad F}} where
-- | And some common notation which may be used.
  module MonadNotation where
    -- η : ∀{𝒞 : 𝒰 (𝑖 ⁺)} {{_ : ICategory 𝒞 𝑖𝑖}} {F : 𝒞 -> 𝒞} {{_ : IMonad F}} -> ∀{A} -> Hom A (F A)
    η : ∀{A} -> Hom A (F A)
    η = return

    -- μ : ∀{𝒞 : 𝒰 (𝑖 ⁺)} {{_ : ICategory 𝒞 𝑖𝑖}} {F : 𝒞 -> 𝒞} {{_ : IMonad F}} -> ∀{A} -> Hom (F (F A)) (F A)
    μ : ∀{A} -> Hom (F (F A)) (F A)
    μ = join

-- | The Kleisli fish, i.e., composition is:
  _>=>_ : ∀{A B C : ⟨ 𝒞 ⟩} -> (f : Hom A (F B)) -> (g : Hom B (F C)) -> Hom A (F C)
  f >=> g = (f ◆ map g) ◆ join

  _=<< : ∀{A B : ⟨ 𝒞 ⟩} -> (A ⟶ F B) -> (F A ⟶ F B)
  f =<< = map f ◆ join


{-
module _ {F : Functor (⌘ 𝒰 𝑖) (⌘ 𝒰 𝑖)} {{_ : IMonad F}} where
  _>>=_ : ∀{A B} -> F A -> (A -> F B) -> F B
  a >>= f = join (map f a)

  _*>_ : ∀{A B} -> F A -> (F B) -> F B
  a *> f = a >>= (λ _ -> f)

  _<*_ : ∀{A B} -> F B -> (F A) -> F B
  a <* f = a >>= (λ x -> f *> return x)

  _>>_ : ∀{A B} -> F A -> (F B) -> F B
  a >> f = a *> f

  >>=/return : ∀{A B} -> (a : A) -> (f : A -> F B) -> return a >>= f ≡ f a
  >>=/return a f = return a >>= f ≡⟨ refl ⟩
                  join (map f (return a)) ≡[ i ]⟨ join (naturality f i a) ⟩
                  join (return (f a)) ≡[ i ]⟨ unit-l-join i (f a) ⟩
                  f a ∎


--- >>=/return-inside : ∀{F : 𝒰₀ -> 𝒰₀} {{_ : IMonad F}} -> ∀{A B : 𝒰₀} -> (a : F A) -> (f : A -> B) -> a >>= (λ x -> return (f x)) ≡ return (f a)
--- >>=/return-inside = ?

  -- comp-Kleisli : ∀{F : 𝒰 𝑖 -> 𝒰 𝑖} {{_ : ISetMonad F}} -> ∀{A B C : 𝒰 𝑖} -> (A -> F B) -> (B -> F C) -> A -> F C
  -- comp-Kleisli f g a = f a >>= g


-- [Definition]
-- | The Kleisli category of a monad \AD{T} is given by:


ICategory:Kleisli : ∀{F : Functor (⌘ 𝒰 𝑖) (⌘ 𝒰 𝑖)} {{_ : IMonad F}} -> ICategory (𝒰 𝑖) (𝑖 , 𝑖)
ICategory:Kleisli = {!!}


-}
-- Hom (ICategory:Kleisli {F = F}) A B = A -> F B
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
-- -- | Wrapped by the following:
module _ {𝒞 : Category 𝑖} where
  Kleisli : ∀(T : Monad 𝒞) -> Category 𝑖
  ⟨ Kleisli T ⟩ = ⟨ 𝒞 ⟩
  ICategory.Hom (of Kleisli T) A B = A ⟶ ⟨ ⟨ T ⟩ ⟩ B
  ICategory._≣_ (of Kleisli T) = _≣_
  ICategory.IEquiv:≣ (of Kleisli T) = IEquiv:≣
  ICategory.id (of Kleisli T) = return
  ICategory._◆_ (of Kleisli T) = _>=>_
  ICategory.unit-l-◆ (of Kleisli T) = {!!}
  ICategory.unit-r-◆ (of Kleisli T) = {!!}
  ICategory.unit-2-◆ (of Kleisli T) = {!!}
  ICategory.assoc-l-◆ (of Kleisli T) = {!!}
  ICategory.assoc-r-◆ (of Kleisli T) = {!!}
  ICategory._◈_ (of Kleisli T) = {!!}
  -- Kleisli T = category _ {{ICategory:Kleisli {F = ⟨ T ⟩}}}
-- -- //

instance
  Index-Notation:Kleisli : Index-Notation (Category 𝑖) (Monad) IAnything (∆ (Category 𝑖))
  (Index-Notation:Kleisli Index-Notation.⌄ 𝒞) T = Kleisli T

