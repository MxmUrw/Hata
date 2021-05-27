
module Verification.Core.Order.Instance.Product where

open import Verification.Conventions
open import Verification.Core.Category.Definition
open import Verification.Core.Category.Instance.Set.Definition
open import Verification.Core.Order.Lattice
open import Verification.Core.Order.Partialorder
open import Verification.Core.Order.Preorder

module _ {A : 𝒰 𝑖} {B : 𝒰 𝑗} {{#A : IPreorder A}} {{#B : IPreorder B}} where
-- module _ {A : Preorder 𝑖} {B : Preorder 𝑗} where
  instance
    IPreorder:× : IPreorder (A ×-𝒰 B)
    IPreorder._≤_ IPreorder:× (a1 , b1) (a2 , b2) = (a1 ≤ a2) ×-𝒰 (b1 ≤ b2)
    IPreorder.refl-≤ IPreorder:× {a = (a , b)} = (refl-≤ {a = a} , refl-≤ {a = b})
    IPreorder.trans-≤ IPreorder:× (p1 , p2) (q1 , q2) = (trans-≤ {{#A}} p1 q1 , trans-≤ {{#B}} p2 q2)



module _ (A : Partialorder 𝑖) (B : Partialorder 𝑗) where
  Partialorder:× : Partialorder (𝑖 ､ 𝑗)
  ⟨ Partialorder:× ⟩ = ⟨ A ⟩ ×-𝒰 ⟨ B ⟩
  IPartialorder.Impl (of Partialorder:×) = IPreorder:× -- (⌘ ⟨ A ⟩) (⌘ ⟨ B ⟩)
  IPartialorder.antisym-≤ (of Partialorder:×) p q = λ i -> (antisym-≤ {{of A}} (p .fst) (q .fst) i , antisym-≤ {{of B}} (p .snd) (q .snd) i)



module _ {A B : 𝒰 𝑖} {{_ : IPreorder A}} {{_ : IPreorder B}} where
  module _ {{_ : has∨-Preorder A}} {{_ : has∨-Preorder B}} where
    instance
      has∨-Preorder:× : has∨-Preorder (A ×-𝒰 B)
      has∨-Preorder._∨_ has∨-Preorder:× (a1 , a2) (b1 , b2) = (a1 ∨ b1 , a2 ∨ b2)
      has∨-Preorder.ι₀-∨ has∨-Preorder:× = (ι₀-∨ , ι₀-∨)
      has∨-Preorder.ι₁-∨ has∨-Preorder:× = (ι₁-∨ , ι₁-∨)
      has∨-Preorder.[_,_]-∨ has∨-Preorder:× = {!!}

  module _ {{_ : has⊥-Preorder A}} {{_ : has⊥-Preorder B}} where
    instance
      has⊥-Preorder:× : has⊥-Preorder (A ×-𝒰 B)
      has⊥-Preorder.⊥ has⊥-Preorder:×         = (⊥ , ⊥)
      has⊥-Preorder.initial-⊥ has⊥-Preorder:× _ = (initial-⊥ _ , initial-⊥ _)
-- module _ (A : JoinLattice 𝑖) (B : JoinLattice 𝑗) where
--   JoinLattice:× : JoinLattice (𝑖 ､ 𝑗)
--   ⟨ JoinLattice:× ⟩ = ⟨ A ⟩ ×-𝒰 ⟨ B ⟩
--   IJoinLattice.Impl (of JoinLattice:×) = of Partialorder:× (` ⟨ A ⟩ `) (` ⟨ B ⟩ `)
--   IJoinLattice._∨_ (of JoinLattice:×) (a1 , a2) (b1 , b2) = (a1 ∨ b1 , a2 ∨ b2)
--   IJoinLattice.ι₀-∨ (of JoinLattice:×) = (ι₀-∨ , ι₀-∨)
--   IJoinLattice.ι₁-∨ (of JoinLattice:×) = (ι₁-∨ , ι₁-∨)
--   IJoinLattice.⊥ (of JoinLattice:×)         = (⊥ , ⊥)
--   IJoinLattice.initial-⊥ (of JoinLattice:×) = (initial-⊥ , initial-⊥)


-- module _ {A : 𝒰 𝑖} {{#A : IPreorder A}} where
--   instance
--     IPreorder:Exp : IPreorder (A ^ n)
--     IPreorder:Exp {n = zero} = IPreorder:⊤
--     IPreorder:Exp {n = suc zero} = #A
--     IPreorder:Exp {n = suc (suc n)} = IPreorder:×
    -- ` A ` (⌘_ (A ^ suc n) {{IPreorder:Exp {n = suc n}}})


-- module _ {A : 𝒰 𝑖} {{#A : IPartialorder A}} where
--   instance
--     IPartialorder:Exp : IPartialorder (A ^ n)
--     IPartialorder:Exp {n = zero} = IPartialorder:⊤
--     IPartialorder:Exp {n = suc zero} = #A
--     IPartialorder:Exp {n = suc (suc n)} = of Partialorder:× ` A ` (⌘_ (A ^ suc n) {{IPartialorder:Exp {n = suc n}}})

-- module _ {A : 𝒰 𝑖} {{#A : IJoinLattice A}} where
--   instance
--     IJoinLattice:Exp : IJoinLattice (A ^ (suc (suc n)))
--     IJoinLattice:Exp {n = zero}= of JoinLattice:× ` A ` ` A `
--     IJoinLattice:Exp {n = suc n}= of JoinLattice:× ` A ` (⌘_ (A ^ (suc (suc n))) {{IJoinLattice:Exp}})
    -- IJoinLattice:Exp {n = zero} = IJoinLattice:⊤
    -- IJoinLattice:Exp {n = suc zero} = #A
    -- IJoinLattice:Exp {n = suc (suc n)} = of JoinLattice:× ` A ` (⌘_ (A ^ suc n) {{IJoinLattice:Exp {n = suc n}}})


