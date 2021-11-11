
module Verification.Core.Category.Std.Functor.Sheaf.Site where

open import Verification.Conventions

open import Verification.Core.Set.Setoid.Definition
open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Category.Std.Functor.Definition


-- ==* Presheaves and sheaves
-- | Similar to how we can define a topology on a set, we can define a "topology" on a category.
-- | Content currently taken mostly from the $\href{https://ncatlab.org/nlab/show/coverage}{nlab article}$.

module _ {𝒞 : 𝒰 _} {{_ : 𝒞 is Category 𝑖}} where
  record isFamilyOver (a : 𝒞) (I : 𝒰 𝑗) : 𝒰 (𝑖 ､ 𝑗) where
    field over : I -> 𝒞
    field fam : ∀ i -> (over i ⟶ a)

  open isFamilyOver {{...}} public

  FamilyOver : ∀ 𝑗 -> (a : 𝒞) -> _
  FamilyOver 𝑗 a = 𝒰 𝑗 :& isFamilyOver a


record isSite (𝑗 : 𝔏 ^ 2) (𝒞 : Category 𝑖) : 𝒰 (𝑖 ､ 𝑗 ⁺) where
  field CoveringIndex : ⟨ 𝒞 ⟩ -> 𝒰 (𝑗 ⌄ 0)
  field Covering : {a : ⟨ 𝒞 ⟩} -> CoveringIndex a -> 𝒰 (𝑗 ⌄ 1)
  field {{Covering:isFamilyOver}} : {a : ⟨ 𝒞 ⟩} -> {I : CoveringIndex a} -> isFamilyOver a (Covering I)
  field coverPullback : ∀{U V : ⟨ 𝒞 ⟩} -> (f : CoveringIndex U) -> (g : V ⟶ U)
                        -> ∑ λ (h : CoveringIndex V) -> ∀(j : Covering h)
                        -> ∑ λ (i : Covering f)
                        -> ∑ λ (k : over j ⟶ over i)
                        -> fam j ◆ g ∼ k ◆ fam i





