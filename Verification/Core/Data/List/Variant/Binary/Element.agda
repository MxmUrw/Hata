
module Verification.Core.Data.List.Variant.Binary.Element where

open import Verification.Core.Conventions
open import Verification.Core.Set.Setoid.Definition
open import Verification.Core.Set.Setoid.Free
-- open import Verification.Core.Data.Prop.Definition
open import Verification.Core.Data.Sum.Definition
open import Verification.Core.Algebra.Monoid.Definition
open import Verification.Core.Data.List.Variant.Binary.Definition
open import Verification.Core.Category.Std.Category.Definition
open import Verification.Core.Category.Std.Morphism.Iso

open import Verification.Core.Data.Indexed.Definition
open import Verification.Core.Data.Indexed.Instance.Monoid
open import Verification.Core.Data.Universe.Everything
open import Verification.Core.Data.Universe.Instance.Semiring


module _ {A : 𝒰 𝑖} where

  el : 𝖥𝗋𝖾𝖾-𝐌𝐨𝐧 A -> 𝐈𝐱 A (𝐔𝐧𝐢𝐯 𝑖)
  el a = indexed (λ i → a ∍ i)

  macro
    𝑒𝑙 = #structureOn el

  private
    lem-1 : ∀{a : 𝖥𝗋𝖾𝖾-𝐌𝐨𝐧 A} -> el (◌ ⋆ a) ≅ el a
    lem-1 {a} = f since P
      where
        f : el (◌ ⋆ a) ⟶ el a
        f _ (right-∍ x) = x

        P = record
            { inverse-◆ = λ _ x -> right-∍ x
            ; inv-r-◆   = λ {i _ (right-∍ x) → right-∍ x}
            ; inv-l-◆   = λ _ -> refl
            }

    lem-2 : ∀{a : 𝖥𝗋𝖾𝖾-𝐌𝐨𝐧 A} -> el (a ⋆ ◌) ≅ el a
    lem-2 {a} = f since P
      where
        f : el (a ⋆ ◌) ⟶ el a
        f _ (left-∍ x) = x

        P = record
            { inverse-◆ = λ _ x -> left-∍ x
            ; inv-r-◆   = λ {i _ (left-∍ x) → left-∍ x}
            ; inv-l-◆   = λ _ -> refl
            }

    lem-3 : ∀{a b c : 𝖥𝗋𝖾𝖾-𝐌𝐨𝐧 A} -> el (a ⋆ b ⋆ c) ≅ el (a ⋆ (b ⋆ c))
    lem-3 {a} {b} {c} = f since P
      where
        f : el (a ⋆ b ⋆ c) ⟶ el (a ⋆ (b ⋆ c))
        f _ (left-∍ (left-∍ x)) = left-∍ x
        f _ (left-∍ (right-∍ x)) = right-∍ (left-∍ x)
        f _ (right-∍ x) = right-∍ (right-∍ x)

        g : el (a ⋆ (b ⋆ c)) ⟶ el (a ⋆ b ⋆ c)
        g _ (left-∍ x) = left-∍ (left-∍ x)
        g _ (right-∍ (left-∍ x)) = left-∍ (right-∍ x)
        g _ (right-∍ (right-∍ x)) = right-∍ x

        P₀ : ∀{a : A} -> (x : (_ ∍ a)) -> g _ (f _ x) ≡ x
        P₀ {a} (left-∍ (left-∍ x)) = refl-≡
        P₀ {a} (left-∍ (right-∍ x)) = refl-≡
        P₀ {a} (right-∍ x) = refl-≡

        P₁ : ∀{a : A} -> (x : (_ ∍ a)) -> f _ (g _ x) ≡ x
        P₁ {a} (left-∍ x) = refl-≡
        P₁ {a} (right-∍ (left-∍ x)) = refl-≡
        P₁ {a} (right-∍ (right-∍ x)) = refl-≡

        P = record
            { inverse-◆ = g
            ; inv-r-◆ = λ _ -> funExt P₀
            ; inv-l-◆ = λ _ -> funExt P₁
            }

    lem-4 : ∀{a b c : 𝖥𝗋𝖾𝖾-𝐌𝐨𝐧 A} -> (el a ≅ el b) -> el (a ⋆ c) ≅ el (b ⋆ c)
    lem-4 {a} {b} {c} f = g since P
      where
        g : el (a ⋆ c) ⟶ el (b ⋆ c)
        g _ (left-∍ x) = left-∍ (⟨ f ⟩ _ x)
        g _ (right-∍ x) = right-∍ x

        h : el (b ⋆ c) ⟶ el (a ⋆ c)
        h _ (left-∍ x) = left-∍ (inverse-◆ (of f) _ x)
        h _ (right-∍ x) = right-∍ x

        P₀ : ∀{a : A} -> (x : (_ ∍ a)) -> h _ (g _ x) ≡ x
        P₀ (left-∍ x) = cong left-∍ (λ i -> inv-r-◆ (of f) _ i x)
        P₀ (right-∍ x) = refl-≡

        P₁ : ∀{a : A} -> (x : (_ ∍ a)) -> g _ (h _ x) ≡ x
        P₁ (left-∍ x) = cong left-∍ (λ i -> inv-l-◆ (of f) _ i x)
        P₁ (right-∍ x) = refl-≡

        P = record
            { inverse-◆ = h
            ; inv-r-◆   = λ _ -> funExt P₀
            ; inv-l-◆   = λ _ -> funExt P₁
            }

    lem-5 : ∀{a b c : 𝖥𝗋𝖾𝖾-𝐌𝐨𝐧 A} -> (el a ≅ el b) -> el (c ⋆ a) ≅ el (c ⋆ b)
    lem-5 {a}{b}{c} f = g since P
      where
        g : el (c ⋆ a) ⟶ el (c ⋆ b)
        g _ (right-∍ x) = right-∍ (⟨ f ⟩ _ x)
        g _ (left-∍ x) = left-∍ x

        h : el (c ⋆ b) ⟶ el (c ⋆ a)
        h _ (right-∍ x) = right-∍ (inverse-◆ (of f) _ x)
        h _ (left-∍ x) = left-∍ x

        P₀ : ∀{a : A} -> (x : (_ ∍ a)) -> h _ (g _ x) ≡ x
        P₀ (left-∍ x) = refl-≡
        P₀ (right-∍ x) = cong right-∍ (λ i -> inv-r-◆ (of f) _ i x)

        P₁ : ∀{a : A} -> (x : (_ ∍ a)) -> g _ (h _ x) ≡ x
        P₁ (left-∍ x) = refl-≡
        P₁ (right-∍ x) = cong right-∍ (λ i -> inv-l-◆ (of f) _ i x)

        P = record
            { inverse-◆ = h
            ; inv-r-◆   = λ _ -> funExt P₀
            ; inv-l-◆   = λ _ -> funExt P₁
            }

    lem-6 : el ◌ ≅ ◌
    lem-6 = f since P
      where
        f : el ◌ ⟶ ◌
        f _ ()

        g : ◌ ⟶ el ◌
        g _ ()

        P = record
            { inverse-◆ = g
            ; inv-r-◆   = λ {_ i ()}
            ; inv-l-◆   = λ {_ i ()}
            }

    lem-7 : ∀{a b : 𝖥𝗋𝖾𝖾-𝐌𝐨𝐧 A} -> el (a ⋆ b) ≅ el a ⋆ el b
    lem-7 {a} {b} = f since P
      where
        f : el (a ⋆ b) ⟶ el a ⋆ el b
        f _ (left-∍ x) = left x
        f _ (right-∍ x) = right x

        g : el a ⋆ el b ⟶ el (a ⋆ b)
        g _ (left x) = left-∍ x
        g _ (just x) = right-∍ x

        P₀ : ∀{a : A} -> (x : (_ ∍ a)) -> g _ (f _ x) ≡ x
        P₀ (left-∍ x)  = refl-≡
        P₀ (right-∍ x) = refl-≡

        P₁ : ∀{a : A} -> (x : (_ ∍ a) + (_ ∍ a)) -> f _ (g _ x) ≡ x
        P₁ (left x)  = refl-≡
        P₁ (right x) = refl-≡

        P = record
            { inverse-◆ = g
            ; inv-r-◆   = λ _ -> funExt P₀
            ; inv-l-◆   = λ _ -> funExt P₁
            }


  instance
    isSetoidHom:el : isSetoidHom (𝖥𝗋𝖾𝖾-𝐌𝐨𝐧 A) (𝐈𝐱 A (𝐔𝐧𝐢𝐯 𝑖)) el
    isSetoidHom:el = record { cong-∼ = rec-RST f}
      where
        f : ∀{a b : 𝖥𝗋𝖾𝖾-𝐌𝐨𝐧 A} -> (a ∼-⋆List b) -> _
        f unit-l-⋆-⧜ = lem-1
        f unit-r-⋆-⧜ = lem-2
        f assoc-l-⋆-⧜ = lem-3
        f (cong-l-⋆-⧜ p) = lem-4 (f p)
        f (cong-r-⋆-⧜ p) = lem-5 (f p)

  instance
    isMonoidHom:el : isMonoidHom (𝖥𝗋𝖾𝖾-𝐌𝐨𝐧 A) (𝐈𝐱 A (𝐔𝐧𝐢𝐯 𝑖)) 𝑒𝑙
    isMonoidHom:el = record
                     { pres-◌ = lem-6
                     ; pres-⋆ = lem-7
                     }


  -- -- setoid hom to 𝐅𝐢𝐧𝐈𝐱
  -- open import Verification.Core.Category.Std.Category.Subcategory.Full
  -- private
  --   instance
  --     _ : isSetoid (𝐅𝐮𝐥𝐥 (𝐈𝐱 A (𝐔𝐧𝐢𝐯 𝑖)) 𝑒𝑙)
  --     _ = isSetoid:byCategory

  -- isSetoidHom:incl-𝖥𝗋𝖾𝖾 : isSetoidHom (𝖥𝗋𝖾𝖾-𝐌𝐨𝐧 A) (𝐅𝐮𝐥𝐥 (𝐈𝐱 A (𝐔𝐧𝐢𝐯 𝑖)) 𝑒𝑙) incl
  -- isSetoidHom:incl-𝖥𝗋𝖾𝖾 = record { cong-∼ = λ p → {!!} }

  identify-∍ : ∀{a b : A} -> incl a ∍ b -> a ≣ b
  identify-∍ incl = refl-≣



