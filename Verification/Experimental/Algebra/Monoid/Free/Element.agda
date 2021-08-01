
module Verification.Experimental.Algebra.Monoid.Free.Element where

open import Verification.Experimental.Conventions
open import Verification.Experimental.Set.Setoid.Definition
open import Verification.Experimental.Set.Setoid.Free
-- open import Verification.Experimental.Data.Prop.Definition
open import Verification.Experimental.Data.Sum.Definition
open import Verification.Experimental.Algebra.Monoid.Definition
open import Verification.Experimental.Algebra.Monoid.Free.Definition
open import Verification.Experimental.Category.Std.Category.Definition
open import Verification.Experimental.Category.Std.Morphism.Iso

open import Verification.Experimental.Data.Indexed.Definition
open import Verification.Experimental.Data.Indexed.Instance.Monoid
open import Verification.Experimental.Data.Universe.Everything
open import Verification.Experimental.Data.Universe.Instance.Semiring


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
        f (right-∍ x) = x

        P = record
            { inverse-◆ = λ x -> right-∍ x
            ; inv-r-◆   = λ {i (right-∍ x) → right-∍ x}
            ; inv-l-◆   = λ {_} -> refl
            }

    lem-2 : ∀{a : 𝖥𝗋𝖾𝖾-𝐌𝐨𝐧 A} -> el (a ⋆ ◌) ≅ el a
    lem-2 {a} = f since P
      where
        f : el (a ⋆ ◌) ⟶ el a
        f (left-∍ x) = x

        P = record
            { inverse-◆ = λ x -> left-∍ x
            ; inv-r-◆   = λ {i (left-∍ x) → left-∍ x}
            ; inv-l-◆   = λ {_} -> refl
            }

    lem-3 : ∀{a b c : 𝖥𝗋𝖾𝖾-𝐌𝐨𝐧 A} -> el (a ⋆ b ⋆ c) ≅ el (a ⋆ (b ⋆ c))
    lem-3 {a} {b} {c} = f since P
      where
        f : el (a ⋆ b ⋆ c) ⟶ el (a ⋆ (b ⋆ c))
        f (left-∍ (left-∍ x)) = left-∍ x
        f (left-∍ (right-∍ x)) = right-∍ (left-∍ x)
        f (right-∍ x) = right-∍ (right-∍ x)

        g : el (a ⋆ (b ⋆ c)) ⟶ el (a ⋆ b ⋆ c)
        g (left-∍ x) = left-∍ (left-∍ x)
        g (right-∍ (left-∍ x)) = left-∍ (right-∍ x)
        g (right-∍ (right-∍ x)) = right-∍ x

        P₀ : ∀{a : A} -> (x : (_ ∍ a)) -> g (f x) ≡ x
        P₀ {a} (left-∍ (left-∍ x)) = refl-≡
        P₀ {a} (left-∍ (right-∍ x)) = refl-≡
        P₀ {a} (right-∍ x) = refl-≡

        P₁ : ∀{a : A} -> (x : (_ ∍ a)) -> f (g x) ≡ x
        P₁ {a} (left-∍ x) = refl-≡
        P₁ {a} (right-∍ (left-∍ x)) = refl-≡
        P₁ {a} (right-∍ (right-∍ x)) = refl-≡

        P = record
            { inverse-◆ = λ {_} -> g
            ; inv-r-◆ = λ {_} -> funExt P₀
            ; inv-l-◆ = λ {_} -> funExt P₁
            }

    lem-4 : ∀{a b c : 𝖥𝗋𝖾𝖾-𝐌𝐨𝐧 A} -> (el a ≅ el b) -> el (a ⋆ c) ≅ el (b ⋆ c)
    lem-4 {a} {b} {c} f = g since P
      where
        g : el (a ⋆ c) ⟶ el (b ⋆ c)
        g (left-∍ x) = left-∍ (⟨ f ⟩ x)
        g (right-∍ x) = right-∍ x

        h : el (b ⋆ c) ⟶ el (a ⋆ c)
        h (left-∍ x) = left-∍ (inverse-◆ (of f) x)
        h (right-∍ x) = right-∍ x

        P₀ : ∀{a : A} -> (x : (_ ∍ a)) -> h (g x) ≡ x
        P₀ (left-∍ x) = cong left-∍ (λ i -> inv-r-◆ (of f) i x)
        P₀ (right-∍ x) = refl-≡

        P₁ : ∀{a : A} -> (x : (_ ∍ a)) -> g (h x) ≡ x
        P₁ (left-∍ x) = cong left-∍ (λ i -> inv-l-◆ (of f) i x)
        P₁ (right-∍ x) = refl-≡

        P = record
            { inverse-◆ = λ {_} -> h
            ; inv-r-◆   = λ {_} -> funExt P₀
            ; inv-l-◆   = λ {_} -> funExt P₁
            }

    lem-5 : ∀{a b c : 𝖥𝗋𝖾𝖾-𝐌𝐨𝐧 A} -> (el a ≅ el b) -> el (c ⋆ a) ≅ el (c ⋆ b)
    lem-5 {a}{b}{c} f = g since P
      where
        g : el (c ⋆ a) ⟶ el (c ⋆ b)
        g (right-∍ x) = right-∍ (⟨ f ⟩ x)
        g (left-∍ x) = left-∍ x

        h : el (c ⋆ b) ⟶ el (c ⋆ a)
        h (right-∍ x) = right-∍ (inverse-◆ (of f) x)
        h (left-∍ x) = left-∍ x

        P₀ : ∀{a : A} -> (x : (_ ∍ a)) -> h (g x) ≡ x
        P₀ (left-∍ x) = refl-≡
        P₀ (right-∍ x) = cong right-∍ (λ i -> inv-r-◆ (of f) i x)

        P₁ : ∀{a : A} -> (x : (_ ∍ a)) -> g (h x) ≡ x
        P₁ (left-∍ x) = refl-≡
        P₁ (right-∍ x) = cong right-∍ (λ i -> inv-l-◆ (of f) i x)

        P = record
            { inverse-◆ = λ {_} -> h
            ; inv-r-◆   = λ {_} -> funExt P₀
            ; inv-l-◆   = λ {_} -> funExt P₁
            }

    lem-6 : el ◌ ≅ ◌
    lem-6 = f since P
      where
        f : el ◌ ⟶ ◌
        f ()

        g : ◌ ⟶ el ◌
        g ()

        P = record
            { inverse-◆ = λ {_} -> g
            ; inv-r-◆   = λ {i ()}
            ; inv-l-◆   = λ {i ()}
            }

    lem-7 : ∀{a b : 𝖥𝗋𝖾𝖾-𝐌𝐨𝐧 A} -> el (a ⋆ b) ≅ el a ⋆ el b
    lem-7 {a} {b} = f since P
      where
        f : el (a ⋆ b) ⟶ el a ⋆ el b
        f (left-∍ x) = left x
        f (right-∍ x) = right x

        g : el a ⋆ el b ⟶ el (a ⋆ b)
        g (left x) = left-∍ x
        g (just x) = right-∍ x

        P₀ : ∀{a : A} -> (x : (_ ∍ a)) -> g (f x) ≡ x
        P₀ (left-∍ x)  = refl-≡
        P₀ (right-∍ x) = refl-≡

        P₁ : ∀{a : A} -> (x : (_ ∍ a) + (_ ∍ a)) -> f (g x) ≡ x
        P₁ (left x)  = refl-≡
        P₁ (right x) = refl-≡

        P = record
            { inverse-◆ = λ {_} -> g
            ; inv-r-◆   = λ {_} -> funExt P₀
            ; inv-l-◆   = λ {_} -> funExt P₁
            }


  instance
    isSetoidHom:el : isSetoidHom (𝖥𝗋𝖾𝖾-𝐌𝐨𝐧 A) (𝐈𝐱 A (𝐔𝐧𝐢𝐯 𝑖)) el
    isSetoidHom:el = record { cong-∼ = rec-RST f}
      where
        f : ∀{a b : 𝖥𝗋𝖾𝖾-𝐌𝐨𝐧 A} -> (a ∼-Free-𝐌𝐨𝐧 b) -> _
        f unit-l-⋆-Free-𝐌𝐨𝐧 = lem-1
        f unit-r-⋆-Free-𝐌𝐨𝐧 = lem-2
        f assoc-l-⋆-Free-𝐌𝐨𝐧 = lem-3
        f (cong-l-⋆-Free-𝐌𝐨𝐧 p) = lem-4 (f p)
        f (cong-r-⋆-Free-𝐌𝐨𝐧 p) = lem-5 (f p)

  instance
    isMonoidHom:el : isMonoidHom (𝖥𝗋𝖾𝖾-𝐌𝐨𝐧 A) (𝐈𝐱 A (𝐔𝐧𝐢𝐯 𝑖)) 𝑒𝑙
    isMonoidHom:el = record
                     { pres-◌ = lem-6
                     ; pres-⋆ = lem-7
                     }







