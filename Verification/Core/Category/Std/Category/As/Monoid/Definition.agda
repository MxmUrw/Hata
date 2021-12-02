
module Verification.Core.Category.Std.Category.As.Monoid.Definition where

open import Verification.Conventions

open import Verification.Core.Set.Setoid.Definition
open import Verification.Core.Set.Discrete
open import Verification.Core.Algebra.Monoid.Definition
open import Verification.Core.Algebra.MonoidWithZero.Definition
open import Verification.Core.Category.Std.Category.Definition

-- open import Verification.Core.Data.Universe.Definition


module _ {𝒞 : 𝒰 𝑖} {{_ : isCategory {𝑗} 𝒞}} where
    -- data isIdArrow {a b : ⟨ 𝒞 ⟩} (f : a ⟶ b)
  isNotIdArrow-impl : {a b : 𝒞} -> (f : a ⟶ b) -> (a ≡-Str b) -> 𝒰 _
  isNotIdArrow-impl f refl-StrId = ¬ (f ∼ id)

  isNotIdArrow : {a b : 𝒞} -> (f : a ⟶ b) -> 𝒰 _
  isNotIdArrow f = ∀(p) -> isNotIdArrow-impl f p

  isIdArrow-impl : {a b : 𝒞} -> (f : a ⟶ b) -> (a ≡-Str b) -> 𝒰 _
  isIdArrow-impl f refl-StrId = f ∼ id

  isIdArrow : {a b : 𝒞} -> (f : a ⟶ b) -> 𝒰 _
  isIdArrow f = ∀(p) -> isIdArrow-impl f p

  rexHom : {a b c : 𝒞} -> (f : a ⟶ b) -> (b ≡-Str c) -> a ⟶ c
  rexHom {a} f p = transport-Str (cong-Str (Hom a) p) f

  lexHom : {a b c : 𝒞} -> (f : b ⟶ c) -> (a ≡-Str b) -> a ⟶ c
  lexHom {a} {b} {c} f refl-≣ = f
  -- transport-Str (cong-Str (λ x -> Hom x c) (p ⁻¹)) f

module _ (𝒞 : Category 𝑖) {{_ : isDiscrete ⟨ 𝒞 ⟩}} where
  data PathMon : 𝒰 𝑖 where
    [] : PathMon
    idp : PathMon
    arrow : {a b : ⟨ 𝒞 ⟩} -> (f : a ⟶ b) -> PathMon

macro
  𝖯𝖺𝗍𝗁𝖬𝗈𝗇 : ∀(𝒞 : Category 𝑖) -> {{_ : isDiscrete ⟨ 𝒞 ⟩}} -> SomeStructure
  𝖯𝖺𝗍𝗁𝖬𝗈𝗇 𝒞 = #structureOn (PathMon 𝒞)

module _ {𝒞 : Category 𝑖} {{_ : isDiscrete ⟨ 𝒞 ⟩}} {{_ : isSet-Str ⟨ 𝒞 ⟩}} where

  data _∼-PathMon_ : (f g : PathMon 𝒞) -> 𝒰 (𝑖) where
    -- idp : ∀{a : ⟨ 𝒞 ⟩} -> {f : a ⟶ a} -> (f ∼ id) -> arrow f ∼-PathMon idp
    idp : idp ∼-PathMon idp
    [] : [] ∼-PathMon []
    arrow : {a b : ⟨ 𝒞 ⟩} -> {f g : a ⟶ b} -> (p : f ∼ g) -> arrow f ∼-PathMon arrow g

  -- instance
  --   isEquivRel:∼-PathMon : isEquivRel (∼-Base _∼-PathMon_)
  --   isEquivRel.refl isEquivRel:∼-PathMon {[]} = incl []
  --   isEquivRel.refl isEquivRel:∼-PathMon {idp} = incl idp
  --   isEquivRel.refl isEquivRel:∼-PathMon {arrow f} = incl (arrow refl)
  --   isEquivRel.sym isEquivRel:∼-PathMon {.idp} (incl idp) = incl idp
  --   isEquivRel.sym isEquivRel:∼-PathMon {.[]} (incl []) = incl []
  --   isEquivRel.sym isEquivRel:∼-PathMon {.(arrow _)} (incl (arrow p)) = incl (arrow (p ⁻¹))
  --   (isEquivRel:∼-PathMon isEquivRel.∙ incl idp) (incl idp) = incl idp
  --   (isEquivRel:∼-PathMon isEquivRel.∙ incl []) (incl []) = incl []
  --   (isEquivRel:∼-PathMon isEquivRel.∙ incl (arrow p)) (incl (arrow q)) = incl (arrow (p ∙ q))

  private
    lem-1 : ∀{a} -> a ∼-PathMon a
    lem-1 {[]} = []
    lem-1 {idp} = idp
    lem-1 {arrow f} = (arrow refl)

    lem-2 : ∀{a b} -> a ∼-PathMon b -> b ∼-PathMon a
    lem-2 {.idp} (idp) = idp
    lem-2 {.[]} ([]) = []
    lem-2 {.(arrow _)} ((arrow p)) = (arrow (p ⁻¹))

    lem-3 : ∀{a b c} -> a ∼-PathMon b -> b ∼-PathMon c -> a ∼-PathMon c
    lem-3 idp idp = idp
    lem-3 [] [] = []
    lem-3 (arrow p) (arrow q) = arrow (p ∙ q)


  instance
    isSetoid:PathMon : isSetoid (PathMon 𝒞)
    isSetoid._∼_ isSetoid:PathMon = _∼-PathMon_
    isSetoid.refl isSetoid:PathMon = lem-1
    isSetoid.sym isSetoid:PathMon = lem-2
    isSetoid._∙_ isSetoid:PathMon = lem-3

  _⋆-PathMon_ : (a b : PathMon 𝒞) -> PathMon 𝒞
  [] ⋆-PathMon b = []
  idp ⋆-PathMon b = b
  arrow f ⋆-PathMon [] = []
  arrow f ⋆-PathMon idp = arrow f
  arrow {a} {b} f ⋆-PathMon arrow {b'} {c} g with (b ≟-Str b')
  ... | yes p = arrow (rexHom f p ◆ g)
  ... | no ¬p = []
  infixl 40 _⋆-PathMon_

  private
    lem-10 : ∀{a : PathMon 𝒞} -> idp ⋆-PathMon a ∼ a
    lem-10 {[]} = refl
    lem-10 {idp} = refl
    lem-10 {arrow f} = refl

    lem-20 : ∀{a : PathMon 𝒞} -> a ⋆-PathMon idp ∼ a
    lem-20 {[]} = refl
    lem-20 {idp} = refl
    lem-20 {arrow f} = refl

    lem-30 : ∀{a b c : PathMon 𝒞} -> (a ⋆-PathMon b) ⋆-PathMon c ∼ a ⋆-PathMon (b ⋆-PathMon c)
    lem-30 {[]} {b} {c} = refl
    lem-30 {idp} {b} {c} = refl
    lem-30 {arrow f} {[]} {c} = refl
    lem-30 {arrow f} {idp} {c} = refl
    lem-30 {arrow {a} {b} f} {arrow {b'} {c} g} {[]} with (b ≟-Str b')
    ... | yes refl-StrId = refl
    ... | no ¬p = refl
    lem-30 {arrow {a} {b} f} {arrow {b'} {c} g} {idp} with (b ≟-Str b')
    ... | yes refl-StrId = refl
    ... | no ¬p = refl
    lem-30 {arrow {a} {b} f} {arrow {b'} {c} g} {arrow {c'} {d} f₁} with (b ≟-Str b') | (c ≟-Str c')
    lem-30 {arrow {a} {b} f} {arrow {b'} {c} g} {arrow {c'} {d} f₁} | yes p0 | yes q0 with (b ≟-Str b') | (c ≟-Str c')
    ... | yes p1 | no ¬q = 𝟘-rec (¬q q0)
    ... | no ¬p | Y = 𝟘-rec (¬p p0)
    ... | yes p1 | yes q1 with isset-Str p0 p1 | isset-Str q0 q1
    ... | refl-StrId | refl-StrId with p0 | q0
    ... | refl-StrId | refl-StrId = (arrow assoc-l-◆)
    lem-30 {arrow {a} {b} f} {arrow {b'} {c} g} {arrow {c'} {d} f₁} | yes refl-StrId | no ¬p with (c ≟-Str c')
    ... | yes p = 𝟘-rec (¬p p)
    ... | no ¬p₁ = refl
    lem-30 {arrow {a} {b} f} {arrow {b'} {c} g} {arrow {c'} {d} f₁} | no ¬p | yes refl-StrId with (b ≟-Str b')
    ... | yes p = 𝟘-rec (¬p p)
    ... | no ¬p₁ = refl
    lem-30 {arrow {a} {b} f} {arrow {b'} {c} g} {arrow {c'} {d} f₁} | no ¬p | no ¬p₁ = refl

    lem-35 : ∀{a0 b0 a1 b1 : PathMon 𝒞} -> (a0 ∼-PathMon a1) -> (b0 ∼-PathMon b1) -> (a0 ⋆-PathMon b0) ∼ (a1 ⋆-PathMon b1)
    lem-35 idp idp = refl
    lem-35 idp [] = refl
    lem-35 idp (arrow p) = (arrow p)
    lem-35 [] q = refl
    lem-35 (arrow p) idp = (arrow p)
    lem-35 (arrow p) [] = refl
    lem-35 (arrow {a} {b} {f0} {f1} p) (arrow {c} {d} {g0} {g1} q) with (b ≟-Str c)
    ... | yes refl-StrId = (arrow (p ◈ q))
    ... | no ¬p = refl

    lem-40 : ∀{a0 b0 a1 b1 : PathMon 𝒞} -> (a0 ∼ a1) -> (b0 ∼ b1) -> (a0 ⋆-PathMon b0) ∼ (a1 ⋆-PathMon b1)
    lem-40 p q = lem-35 p q

  instance
    isMonoid:PathMon : isMonoid (𝖯𝖺𝗍𝗁𝖬𝗈𝗇 𝒞)
    isMonoid._⋆_ isMonoid:PathMon = _⋆-PathMon_
    isMonoid.◌ isMonoid:PathMon = idp
    isMonoid.unit-l-⋆ isMonoid:PathMon = lem-10
    isMonoid.unit-r-⋆ isMonoid:PathMon = lem-20
    isMonoid.assoc-l-⋆ isMonoid:PathMon {a} {b} {c} = lem-30 {a} {b} {c}
    -- isMonoid.assoc-r-⋆ isMonoid:PathMon {a} {b} {c} = lem-30 {a} {b} {c} ⁻¹
    isMonoid._≀⋆≀_ isMonoid:PathMon = lem-40


  instance
    hasZero:PathMon : hasZero (𝖯𝖺𝗍𝗁𝖬𝗈𝗇 𝒞)
    hasZero.◍ hasZero:PathMon = []
    hasZero.absorb-r-⋆ hasZero:PathMon {[]} = refl
    hasZero.absorb-r-⋆ hasZero:PathMon {idp} = refl
    hasZero.absorb-r-⋆ hasZero:PathMon {arrow f} = refl
    hasZero.absorb-l-⋆ hasZero:PathMon = refl
    hasZero.decide-◍ hasZero:PathMon [] = right refl
    hasZero.decide-◍ hasZero:PathMon idp = left (λ ())
    hasZero.decide-◍ hasZero:PathMon (arrow f) = left (λ ())



  -- further statements
  functoriality-arrow : ∀{a b c : ⟨ 𝒞 ⟩} -> (f : a ⟶ b) -> (g : b ⟶ c) -> arrow (f ◆ g) ∼ (arrow f ⋆ arrow g)
  functoriality-arrow {a} {b} {c} f g with (b ≟-Str b)
  ... | yes p = let P₀ : refl-StrId ≡-Str p
                    P₀ = isset-Str _ _
                in (transport-Str (cong-Str (λ q -> arrow (f ◆ g) ∼ arrow (rexHom f q ◆ g)) P₀) refl)
  ... | no ¬p = 𝟘-rec (¬p refl-≣)

  PathMon-non-matching-arrows : ∀{a b c d : ⟨ 𝒞 ⟩} -> (b ≢-Str c) -> (f : a ⟶ b) -> (g : c ⟶ d) -> arrow f ⋆ arrow g ∼ []
  PathMon-non-matching-arrows {a} {b} {c} {d} p f g with (b ≟-Str c)
  ... | yes q = 𝟘-rec (p q)
  ... | no ¬p = refl

  PathMon-arrow-path-inv : ∀{a b c d : ⟨ 𝒞 ⟩} -> (f : a ⟶ b) -> (g : c ⟶ d) -> (p : a ≡-Str c) -> (q : b ≡-Str d) -> (arrow {𝒞 = 𝒞} f ∼-PathMon arrow g) -> rexHom f q ∼ lexHom g p
  PathMon-arrow-path-inv f g p q (arrow P) =
    let P₀ : rexHom f refl-≣ ∼ lexHom g refl-≣
        P₀ = P
        q₀ : refl-≣ ≡-Str q
        q₀ = isset-Str _ _
        q₁ : refl-≣ ≡-Str p
        q₁ = isset-Str _ _
        P₁ : rexHom f q ∼ lexHom g refl-≣
        P₁ = transport-Str (cong-Str (λ ξ -> rexHom f ξ ∼ lexHom g refl-≣) q₀) P₀
        P₂ : rexHom f q ∼ lexHom g p
        P₂ = transport-Str (cong-Str (λ ξ -> rexHom f q ∼ lexHom g ξ) q₁) P₁
    in P₂

  case-PathMon_of : ∀(x : PathMon 𝒞) -> {P : PathMon 𝒞 -> 𝒰 𝑘}
                  -> (∀(p : x ∼ []) -> P x)
                  -> (∀(p : x ∼ idp) -> P x)
                  -> (∀{a b : ⟨ 𝒞 ⟩} {f : a ⟶ b} -> (p : x ∼ arrow f) -> P x)
                  -> P x
  case-PathMon [] of {P} f1 f2 f3 = f1 refl
  case-PathMon idp of {P} f1 f2 f3 = f2 refl
  case-PathMon arrow f of {P} f1 f2 f3 = f3 refl

  PathMon-arrow-path-matching-codom : ∀{a b c d : ⟨ 𝒞 ⟩} -> (f : a ⟶ b) -> (g : c ⟶ d) -> (arrow {𝒞 = 𝒞} f ∼-PathMon arrow g) -> b ≡-Str d
  PathMon-arrow-path-matching-codom f g (arrow p) = refl-≣
