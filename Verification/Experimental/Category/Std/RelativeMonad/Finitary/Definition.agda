
module Verification.Experimental.Category.Std.RelativeMonad.Finitary.Definition where

open import Verification.Conventions

open import Verification.Experimental.Data.Nat.Free
open import Verification.Experimental.Set.Setoid
open import Verification.Experimental.Category.Std.Category.Definition
open import Verification.Experimental.Category.Std.Functor.Definition
open import Verification.Experimental.Category.Std.Functor.Instance.Category
open import Verification.Experimental.Category.Std.Natural.Definition
open import Verification.Experimental.Category.Std.Category.Instance.Category

open import Verification.Experimental.Category.Std.RelativeMonad.Definition
open import Verification.Experimental.Category.Std.Monad.Definition

open import Verification.Experimental.Data.Indexed.Duplicate
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



module mytestwhat {𝑖 : 𝔏} (J : 𝒰 𝑗) where
  bla : (Functor (𝐈𝐱 J (𝐔𝐧𝐢𝐯 𝑖)) (𝐈𝐱 J (𝐔𝐧𝐢𝐯 𝑖))) -> ℕ
  bla = {!!}

 -- {a b : 𝐈𝐱𝐌𝐧𝐝 𝑖} (f : a ⟶ b)
module _ (J : 𝒰 𝑗) where
  record hasPseudoInverse {𝑖 : 𝔏} : 𝒰 (join-𝔏 (𝑖 ⁺) 𝑗) where
    -- field testaa : (Indexed (J) (𝒰 𝑖 since isCategory:𝒰)) -> (Indexed (J) (𝒰 𝑖 since {!!}))
    field PIErr : Functor (𝐈𝐱 J (𝐔𝐧𝐢𝐯 𝑖)) (𝐈𝐱 J (𝐔𝐧𝐢𝐯 𝑖))

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


  module _ {Mᵘ : FinitaryRelativeMonad I} where

    private
      macro M = #structureOn ⟨ Mᵘ ⟩

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

    -- isFunctor:M : isFunctor _ _ ⟨ M ⟩
    -- isFunctor:M = it

    pure-Re⁻¹ : ∀(a : 𝐈𝐱 I (𝐔𝐧𝐢𝐯 𝑖)) -> a ⟶ Re⁻¹ M a
    pure-Re⁻¹ a i x = rel⁻¹ (incl (incl i)) (repure i incl) (λ {i₁ incl → x})

    join-Re⁻¹ : ∀(a : 𝐈𝐱 I (𝐔𝐧𝐢𝐯 𝑖)) -> Re⁻¹ M (Re⁻¹ M a) ⟶ Re⁻¹ M a
    join-Re⁻¹ _ i (rel⁻¹ as term values) =
      let

        -- the map `values` which gives us a `Re⁻¹ M a` value for every `a` in `as`,
        -- can be projected to give us only the list of holes of the monad for a given `a`
        j : [ ⟨ as ⟩ ]ᶠ -> 𝐅𝐢𝐧𝐈𝐱 I
        j = (λ (a , ap) → values a ap .fst)

        -- the sum of all these lists is the sum in the `𝐅𝐢𝐧𝐈𝐱` category
        ⨆j = ⨆ᶠ (indexed j)

        -- the `snd` part of the `Re⁻¹ M a` value then gives us a `M ?` value
        -- for each a in as
        terms : ∀ (a : [ ⟨ as ⟩ ]ᶠ) -> ix (M (j a)) (fst a)
        terms = λ(a , ap) -> values a ap .snd

        -- we do have the injection functions
        ι-j : ∀(a : [ ⟨ as ⟩ ]ᶠ) -> j a ⟶ ⨆j
        ι-j = {!!}

        -- with which we can extend the terms
        terms' : ∀ (a : [ ⟨ as ⟩ ]ᶠ) -> ix (M ⨆j) (fst a)
        terms' = λ a -> (mapOf M) (ι-j a) _ (terms a)

        -- these terms, since the dependency on a in the `⨆j` index of the monad
        -- is now gone, can be seen as morphisms in `𝐈𝐱`
        terms₂ : 𝑓𝑖𝑛 I as ⟶ M ⨆j
        terms₂ = λ a ap → terms' (a , ap)

        -- and can be lifted to a morphism on monads
        terms₃ : M as ⟶ M ⨆j
        terms₃ = reext terms₂

        -- which can finally be applied to the term value which we have,
        -- thus substituting the holes of the top level term with the smaller
        -- values for them
        term' : ix (M ⨆j) i
        term' = terms₃ i term


      in rel⁻¹ ⨆j term' {!!}


    instance
      isMonad:Re⁻¹ : isMonad (Re⁻¹ M)
      isMonad.pure isMonad:Re⁻¹ = pure-Re⁻¹
      isMonad.join isMonad:Re⁻¹ = join-Re⁻¹
      isMonad.isNatural:pure isMonad:Re⁻¹ = {!!}
      isMonad.isNatural:join isMonad:Re⁻¹ = {!!}
      isMonad.unit-l-join isMonad:Re⁻¹ = {!!}
      isMonad.unit-r-join isMonad:Re⁻¹ = {!!}
      isMonad.assoc-join isMonad:Re⁻¹ = {!!}




