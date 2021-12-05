
module Verification.Core.Category.Std.RelativeMonad.Finitary.Construction.Abstracted where

open import Verification.Conventions hiding (_⊔_)

open import Verification.Core.Set.Setoid
open import Verification.Core.Data.AllOf.Collection.Basics
open import Verification.Core.Data.AllOf.Collection.TermTools
open import Verification.Core.Category.Std.AllOf.Collection.Basics
open import Verification.Core.Category.Std.AllOf.Collection.Limits

open import Verification.Core.Category.Std.RelativeMonad.Definition
-- open import Verification.Core.Category.Std.Monad.Definition

open import Verification.Core.Data.Indexed.Duplicate
open import Verification.Core.Data.Indexed.Definition
open import Verification.Core.Data.FiniteIndexed.Definition
-- open import Verification.Core.Data.FiniteIndexed.Instance.Category
open import Verification.Core.Category.Std.Category.Subcategory.Full

open import Verification.Core.Algebra.Monoid.Definition
open import Verification.Core.Algebra.Monoid.Free
open import Verification.Core.Data.List.Variant.Binary.Element

open import Verification.Core.Category.Std.RelativeMonad.Finitary.Definition




-----------------------------------------
-- NOTE: it seems that this concept does
--       not work.
--
-- At least, it is likely that there is no
-- monad instance here. The problem is that
-- when defining substitution (reext), that
-- we have to substitute quantified terms.
-- But since we do not have quantifications
-- on the inside, we need to move them to the outside.
-- Even if this works, this is rather messy,
-- since then all the quantifications of all
-- the terms to be substituted accumulate.
--

module _ {I : 𝒰 𝑖} (t' : FinitaryRelativeMonad I) where

  private macro t = #structureOn ⟨ t' ⟩

  record Abstractedᵈ (a : 𝐅𝐢𝐧𝐈𝐱 I) (i : I) : 𝒰 𝑖 where
    constructor ∀[_]_
    field fst : 𝐅𝐢𝐧𝐈𝐱 I
    field snd : t (a ⊔ fst) ⌄ i


  𝑎𝑏𝑠𝑡ᵘ : 𝐅𝐢𝐧𝐈𝐱 I -> 𝐈𝐱 I (𝐔𝐧𝐢𝐯 𝑖)
  𝑎𝑏𝑠𝑡ᵘ = indexed ∘ Abstractedᵈ

  macro 𝑎𝑏𝑠𝑡 = #structureOn 𝑎𝑏𝑠𝑡ᵘ

module _ {I : 𝒰 𝑖} {t' : FinitaryRelativeMonad I} where
  private macro t = #structureOn ⟨ t' ⟩

  map-𝑎𝑏𝑠𝑡 : ∀{a b : 𝐅𝐢𝐧𝐈𝐱 I} -> a ⟶ b -> 𝑎𝑏𝑠𝑡 t a ⟶ 𝑎𝑏𝑠𝑡 t b
  map-𝑎𝑏𝑠𝑡 f i (∀[ x ] term)= ∀[ x ] mapOf t (f ⇃⊔⇂ id) i term

  instance
    isFunctor:Abstracted : isFunctor (𝐅𝐢𝐧𝐈𝐱 I) (𝐈𝐱 I (𝐔𝐧𝐢𝐯 𝑖)) (𝑎𝑏𝑠𝑡 t)
    isFunctor.map isFunctor:Abstracted = map-𝑎𝑏𝑠𝑡
    isFunctor.isSetoidHom:map isFunctor:Abstracted = {!!}
    isFunctor.functoriality-id isFunctor:Abstracted = {!!}
    isFunctor.functoriality-◆ isFunctor:Abstracted = {!!}

  repure-𝑎𝑏𝑠𝑡 : ∀ {a} -> 𝑓𝑖𝑛 I a ⟶ 𝑎𝑏𝑠𝑡 t a
  repure-𝑎𝑏𝑠𝑡 i x = ∀[ ⊥ ] (mapOf t ι₀ i (repure i x))

  reext-𝑎𝑏𝑠𝑡 : ∀ {a b} -> 𝑓𝑖𝑛 I a ⟶ 𝑎𝑏𝑠𝑡 t b -> 𝑎𝑏𝑠𝑡 t a ⟶ 𝑎𝑏𝑠𝑡 t b
  reext-𝑎𝑏𝑠𝑡 f i (∀[ v ] term) = ∀[ v ] (reext {!!} i term)


  instance
    isRelativeMonad:𝑎𝑏𝑠𝑡 : isRelativeMonad (𝑓𝑖𝑛 I) (𝑎𝑏𝑠𝑡 t)
    isRelativeMonad.repure isRelativeMonad:𝑎𝑏𝑠𝑡 = repure-𝑎𝑏𝑠𝑡
    isRelativeMonad.reext isRelativeMonad:𝑎𝑏𝑠𝑡 = reext-𝑎𝑏𝑠𝑡
    isRelativeMonad.reunit-l isRelativeMonad:𝑎𝑏𝑠𝑡 = {!!}
    isRelativeMonad.reunit-r isRelativeMonad:𝑎𝑏𝑠𝑡 = {!!}
    isRelativeMonad.reassoc isRelativeMonad:𝑎𝑏𝑠𝑡 = {!!}


