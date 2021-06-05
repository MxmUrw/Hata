
module Verification.Experimental.Theory.Formal.Presentation.Signature.SingleSorted.Instance.Functor where

open import Verification.Experimental.Conventions
open import Verification.Experimental.Set.Setoid
open import Verification.Experimental.Set.Setoid.Instance.Category
open import Verification.Experimental.Data.Universe.Everything
open import Verification.Experimental.Data.Universe.Instance.Category
open import Verification.Experimental.Category.Std.Category.Definition
open import Verification.Experimental.Category.Std.Functor.Definition
open import Verification.Experimental.Category.Std.Monad.Definition
open import Verification.Experimental.Theory.Formal.Presentation.Signature.SingleSorted.Definition
-- open import Verification.Experimental.Theory.Presentation.Signature.SingleSorted.Instance.Setoid


module _ {σ : Signature} {A B : 𝐓𝐲𝐩𝐞 𝑖} where
  mutual
    map-Term : (f : A -> B) -> Term σ A -> Term σ B
    map-Term f (te a ts) = te a (map-Terms f ts)
    map-Term f (var x) = var (f x)

    map-Terms : (f : A -> B) -> Terms σ A n -> Terms σ B n
    map-Terms f [] = []
    map-Terms f (t ∷ ts) = map-Term f t ∷ map-Terms f ts


instance
  isFunctor:Term : ∀{σ : Signature} -> isFunctor (𝐓𝐲𝐩𝐞 𝑖) (𝐓𝐲𝐩𝐞 𝑖) (Term σ)
  isFunctor.map isFunctor:Term f = incl (map-Term ⟨ f ⟩)
  isFunctor.isSetoidHom:map isFunctor:Term = {!!}
  isFunctor.functoriality-id isFunctor:Term = {!!}
  isFunctor.functoriality-◆ isFunctor:Term = {!!}

-- 𝑇𝑒𝑟𝑚 = 𝐓𝐞𝐫𝐦

-- Subs = 𝐓𝐲𝐩𝐞 ⌄ 𝑇𝑒𝑟𝑚


-- module _ {σ} where
--   Y : 𝐓𝐲𝐩𝐞 (ℓ₀)
--   Y = 𝑇𝑒𝑟𝑚 σ (Fin 1)


-- XX : Functor (𝐓𝐲𝐩𝐞 𝑖) (𝐓𝐲𝐩𝐞 𝑖)
-- XX = 𝑇𝑒𝑟𝑚 {!!}


-- 𝐓𝐞𝐫𝐦 {!!}

-- 𝑇𝑒𝑟𝑚 

-- \nctype
-- \nfterm




--   instance
--     isSetoidHom:map-Term : ∀{f : SetoidHom A B} -> isSetoidHom (TermF 𝑖 σ A) (TermF 𝑖 σ B) (map-Term f)
--     isSetoidHom.preserves-∼ isSetoidHom:map-Term = {!!}


-- instance
--   isFunctor:TermF : ∀{σ : Signature} -> isFunctor (Std _) (Std _) (TermF 𝑖 σ)
--   isFunctor.map (isFunctor:TermF {σ}) f = incl ′ map-Term ⟨ f ⟩ ′
--   isFunctor.isSetoidHom:map isFunctor:TermF = {!!}
--   isFunctor.functoriality-id isFunctor:TermF = {!!}
--   isFunctor.functoriality-◆ isFunctor:TermF = {!!}






