
module Verification.Core.Category.Std.Functor.Equivalence.Definition where

open import Verification.Conventions

open import Verification.Core.Set.Setoid.Definition
open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Category.Std.Category.Notation.Associativity
open import Verification.Core.Category.Std.Category.Instance.Category
open import Verification.Core.Category.Std.Morphism.Iso
open import Verification.Core.Category.Std.Functor.Definition
open import Verification.Core.Category.Std.Functor.Instance.Category
open import Verification.Core.Set.Setoid.Morphism
open import Verification.Core.Category.Std.Functor.Image
open import Verification.Core.Category.Std.Functor.EssentiallySurjective
open import Verification.Core.Category.Std.Functor.Faithful
open import Verification.Core.Category.Std.Functor.Full
open import Verification.Core.Category.Std.Natural.Definition
open import Verification.Core.Category.Std.Natural.Instance.Setoid


module _ {𝒞 : Category 𝑖} {𝒟 : Category 𝑗} where
  record isIso-𝐂𝐚𝐭 (F : Functor 𝒞 𝒟) : 𝒰 (𝑖 ､ 𝑗) where
    field inverse-◆-𝐂𝐚𝐭 : Functor 𝒟 𝒞
    field inv-r-◆-𝐂𝐚𝐭 : F ◆-𝐂𝐚𝐭 inverse-◆-𝐂𝐚𝐭 ∼ id
    field inv-l-◆-𝐂𝐚𝐭 : inverse-◆-𝐂𝐚𝐭 ◆-𝐂𝐚𝐭 F ∼ id

  open isIso-𝐂𝐚𝐭 public

module _ (𝒞 : Category 𝑖) (𝒟 : Category 𝑗) where
  _≅-𝐂𝐚𝐭_ = (Functor 𝒞 𝒟) :& isIso-𝐂𝐚𝐭

pattern _since_andAlso_ a b c = ′_′ a {make∑i {{b}}} {{c}}

module _ {𝒞 : Category 𝑖} {𝒟 : Category 𝑗} where
  sym-≅-𝐂𝐚𝐭 : 𝒞 ≅-𝐂𝐚𝐭 𝒟 -> 𝒟 ≅-𝐂𝐚𝐭 𝒞
  sym-≅-𝐂𝐚𝐭 p = ⟨ inverse-◆-𝐂𝐚𝐭 (of p) ⟩ since of inverse-◆-𝐂𝐚𝐭 (of p) andAlso record
    { inverse-◆-𝐂𝐚𝐭 = ⟨ p ⟩ since it
    ; inv-r-◆-𝐂𝐚𝐭 = inv-l-◆-𝐂𝐚𝐭 (of p)
    ; inv-l-◆-𝐂𝐚𝐭 = inv-r-◆-𝐂𝐚𝐭 (of p)
    }
