
module Verification.Core.Set.Decidable where

open import Verification.Conventions
open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Category.Std.Morphism.Iso
open import Verification.Core.Data.Universe.Definition
open import Verification.Core.Data.Universe.Instance.Category

-- open import Verification.Core.Data.Prop.Everything

isDecidable : ∀(A : 𝒰 𝑖) -> 𝒰 _
isDecidable A = (¬ A) +-𝒰 A

case-Decision_of : ∀{A : 𝒰 𝑖} -> (a : Decision A) -> {P : Decision A -> 𝒰 𝑗}
                   -> (∀ a -> P (no a))
                   -> (∀ a -> P (yes a))
                   -> P a
case-Decision no ¬p of f1 f2 = f1 ¬p
case-Decision yes p of f1 f2 = f2 p


private
  lem-0 : ∀{A : 𝒰 𝑖} (f g : A -> 𝟘-𝒰) -> f ≡ g
  lem-0 f g i x with f x
  ... | ()


module _ {A : 𝒰 𝑖} where
  record isDecFam (P : A -> 𝒰 𝑗) : 𝒰 (𝑖 ､ 𝑗) where
    field isProp:DecFam : ∀{a} -> isProp (P a)
    field decide-Fam : ∀(a : A) -> isDecidable (P a)

  open isDecFam {{...}} public


  module _ (P : A -> 𝒰 𝑖) {{_ : isDecFam P}} where
    split-Fam : A ≅ ((∑ (λ a -> ¬ (P a))) +-𝒰 (∑ P))
    split-Fam = f since Q
      where
        f : A -> ((∑ (λ a -> ¬ (P a))) +-𝒰 (∑ P))
        f a with decide-Fam a
        ... | left x = left (_ , x)
        ... | just x = right (_ , x)

        g : ((∑ (λ a -> ¬ (P a))) +-𝒰 (∑ P)) -> A
        g (left (x , _)) = x
        g (just (x , _)) = x

        lem-1 : ∀ a -> g (f a) ≡ a
        lem-1 a with decide-Fam a
        ... | left x = refl-≡
        ... | just x = refl-≡

        lem-2 : ∀ a -> f (g a) ≡ a
        lem-2 (left (x , xp)) with decide-Fam x
        ... | left xp2 = λ i → left (x , lem-0 xp2 xp i)
        ... | just xp2 = 𝟘-rec (xp xp2)
        lem-2 (just (x , xp)) with decide-Fam x
        ... | left xp2 = 𝟘-rec (xp2 xp)
        ... | just xp2 = λ i -> right (x , isProp:DecFam xp2 xp i)

        Q : isIso (hom f)
        Q = record
            { inverse-◆ = g
            ; inv-r-◆ = funExt lem-1
            ; inv-l-◆ = funExt lem-2
            }




