
module Verification.Experimental.Category.Std.RelativeMonad.Finitary.Definition where

open import Verification.Conventions

open import Verification.Experimental.Set.Setoid
open import Verification.Experimental.Category.Std.Category.Definition
open import Verification.Experimental.Category.Std.Functor.Definition
open import Verification.Experimental.Category.Std.Functor.Instance.Category
open import Verification.Experimental.Category.Std.Natural.Definition
open import Verification.Experimental.Category.Std.Category.Instance.Category

open import Verification.Experimental.Category.Std.RelativeMonad.Definition
open import Verification.Experimental.Category.Std.Monad.Definition

open import Verification.Experimental.Data.Indexed.Definition
open import Verification.Experimental.Data.FiniteIndexed.Definition
open import Verification.Experimental.Data.Universe.Everything
open import Verification.Experimental.Category.Std.Category.Subcategory.Full

open import Verification.Experimental.Algebra.Monoid.Free
open import Verification.Experimental.Algebra.Monoid.Free.Element


module _ (I : 𝒰 𝑖) where
  private
    fin : 𝐅𝐢𝐧𝐈𝐱 I -> (𝐈𝐱 I (𝐔𝐧𝐢𝐯 𝑖))
    fin = 𝑓𝑢𝑙𝑙 _ 𝑒𝑙
  macro
    𝑓𝑖𝑛 = #structureOn fin

  FinitaryRelativeMonad : 𝒰 _
  FinitaryRelativeMonad = RelativeMonad 𝑓𝑖𝑛



-----------------------------------------
-- making finitary relative (sorted) monads into real monads

module _ {I : 𝒰 𝑖} where
  record Re⁻¹ᵈ (M : FinitaryRelativeMonad I) (A : 𝐈𝐱 I (𝐔𝐧𝐢𝐯 𝑖)) (i : I) : 𝒰 𝑖 where
    constructor rel⁻¹
    field fst : 𝐅𝐢𝐧𝐈𝐱 I
    field snd : ix (⟨ M ⟩ fst) i
    field thd : 𝑓𝑖𝑛 I fst ⟶ A

  open Re⁻¹ᵈ public

  module _ (M : FinitaryRelativeMonad I) where
    Re⁻¹ᵘ : (A : 𝐈𝐱 I (𝐔𝐧𝐢𝐯 𝑖)) -> 𝐈𝐱 I (𝐔𝐧𝐢𝐯 𝑖)
    Re⁻¹ᵘ A = indexed (Re⁻¹ᵈ M A)

    macro Re⁻¹ = #structureOn Re⁻¹ᵘ


  module _ {M : FinitaryRelativeMonad I} where

    map-Re⁻¹ : ∀{a b : 𝐈𝐱 I (𝐔𝐧𝐢𝐯 𝑖)} -> (a ⟶ b) -> Re⁻¹ M a ⟶ Re⁻¹ M b
    map-Re⁻¹ f i (rel⁻¹ as term values) = rel⁻¹ as term (values ◆ f)

    instance
      isSetoidHom:map-Re⁻¹ : ∀{a b : 𝐈𝐱 I (𝐔𝐧𝐢𝐯 𝑖)} -> isSetoidHom ′ IndexedHom a b ′ ′ IndexedHom (Re⁻¹ᵘ M a) (Re⁻¹ᵘ M b) ′ map-Re⁻¹
      isSetoidHom:map-Re⁻¹ = record { cong-∼ = λ x i j → map-Re⁻¹ (funExt x j) i }


    instance
      isFunctor:Re⁻¹ : isFunctor (𝐈𝐱 I (𝐔𝐧𝐢𝐯 𝑖)) (𝐈𝐱 I (𝐔𝐧𝐢𝐯 𝑖)) (Re⁻¹ M)
      isFunctor.map isFunctor:Re⁻¹ = map-Re⁻¹
      isFunctor.isSetoidHom:map isFunctor:Re⁻¹ = it
      isFunctor.functoriality-id isFunctor:Re⁻¹ = λ i → refl-≡
      isFunctor.functoriality-◆ isFunctor:Re⁻¹ = λ i → refl-≡

    pure-Re⁻¹ : ∀{a : 𝐈𝐱 I (𝐔𝐧𝐢𝐯 𝑖)} -> a ⟶ Re⁻¹ M a
    pure-Re⁻¹ i x = rel⁻¹ (incl (incl i)) (repure i incl) (λ {i₁ incl → x})

    join-Re⁻¹ : ∀{a : 𝐈𝐱 I (𝐔𝐧𝐢𝐯 𝑖)} -> Re⁻¹ M (Re⁻¹ M a) ⟶ Re⁻¹ M a
    join-Re⁻¹ i (rel⁻¹ as term values) = rel⁻¹ as term {!!}

    instance
      isMonad:Re⁻¹ : isMonad (Re⁻¹ M)
      isMonad.pure isMonad:Re⁻¹ = pure-Re⁻¹
      isMonad.join isMonad:Re⁻¹ = join-Re⁻¹
      isMonad.isNatural:pure isMonad:Re⁻¹ = {!!}
      isMonad.isNatural:join isMonad:Re⁻¹ = {!!}
      isMonad.unit-l-join isMonad:Re⁻¹ = {!!}
      isMonad.unit-r-join isMonad:Re⁻¹ = {!!}
      isMonad.assoc-join isMonad:Re⁻¹ = {!!}




