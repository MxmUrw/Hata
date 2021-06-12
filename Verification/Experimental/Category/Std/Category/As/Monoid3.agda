
module Verification.Experimental.Category.Std.Category.As.Monoid3 where

open import Verification.Conventions

open import Verification.Experimental.Set.Setoid.Definition
open import Verification.Experimental.Set.Discrete
open import Verification.Experimental.Algebra.Monoid.Definition
open import Verification.Experimental.Category.Std.Category.Definition

-- open import Verification.Experimental.Data.Universe.Definition


module _ {A : 𝒰 𝑖} (R : A -> A -> 𝒰 𝑗) where
  data RST : A -> A -> 𝒰 (𝑖 ､ 𝑗) where
    ι-RST : ∀{a b} -> R a b -> RST a b
    refl-RST : ∀{a} -> RST a a
    sym-RST : ∀{a b} -> RST a b -> RST b a
    _∙-RST_ : ∀{a b c} -> RST a b -> RST b c -> RST a c

module _ {A : 𝒰 𝑖} {R : A -> A -> 𝒰 𝑗} where
  instance
    isEquivRel:RST : isEquivRel (∼-Base (RST R))
    isEquivRel.refl isEquivRel:RST = incl refl-RST
    isEquivRel.sym isEquivRel:RST p = incl (sym-RST ⟨ p ⟩)
    isEquivRel._∙_ isEquivRel:RST p q = incl (⟨ p ⟩ ∙-RST ⟨ q ⟩)

module _ {𝒞 : 𝒰 𝑖} {{_ : isCategory 𝑗 𝒞}} where
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

module _ (𝒞 : Category 𝑖) {{_ : isDiscrete ⟨ 𝒞 ⟩}} where
  data PathMon : 𝒰 𝑖 where
    [] : PathMon
    idp : PathMon
    arrow : {a b : ⟨ 𝒞 ⟩} -> (f : a ⟶ b) -> (isNotIdArrow f) -> PathMon


module _ {𝒞 : Category 𝑖} {{_ : isDiscrete ⟨ 𝒞 ⟩}} {{_ : isSet-Str ⟨ 𝒞 ⟩}} {{_ : ∀{a b : ⟨ 𝒞 ⟩} -> isDiscrete-∼ (a ⟶ b)}} where


  data _∼-PathMon_ : (f g : PathMon 𝒞) -> 𝒰 (𝑖) where
    -- idp : ∀{a : ⟨ 𝒞 ⟩} -> {f : a ⟶ a} -> (f ∼ id) -> arrow f ∼-PathMon idp
    arrow : {a b : ⟨ 𝒞 ⟩} -> {f g : a ⟶ b} -> (fP : isNotIdArrow f) -> (gP : isNotIdArrow g) -> (p : f ∼ g) -> arrow f fP ∼-PathMon arrow g gP


  instance
    isSetoid:PathMon : isSetoid _ (PathMon 𝒞)
    isSetoid._∼'_ isSetoid:PathMon = RST _∼-PathMon_
    isSetoid.isEquivRel:∼ isSetoid:PathMon = it

  data ComposeCheckIdResult {a b c d : ⟨ 𝒞 ⟩} (f : a ⟶ b) (g : c ⟶ d) (p : b ≡-Str c) (q : d ≡-Str a) : 𝒰 𝑖 where
    composeNotId : isNotIdArrow (rexHom f p ◆ g) -> ComposeCheckIdResult f g p q
    composeIsId : isIdArrow (rexHom f p ◆ rexHom g q) -> ComposeCheckIdResult f g p q

  composeCheckId : ∀{a b c d : ⟨ 𝒞 ⟩} -> (f : a ⟶ b) (g : c ⟶ d) -> (p : b ≡-Str c) -> (q : d ≡-Str a) -> ComposeCheckIdResult f g p q
  composeCheckId f g refl-StrId refl-StrId with (f ◆ g ≟-∼ id)
  ... | yes p = composeIsId (λ q -> let P₀ : refl-StrId ≡-Str q
                                        P₀ = isset-Str _ _
                                    in transport-Str (cong-Str (isIdArrow-impl (f ◆ g)) P₀) p)
  ... | no ¬p = composeNotId (λ q -> let P₀ : refl-StrId ≡-Str q
                                         P₀ = isset-Str _ _
                                     in transport-Str (cong-Str (isNotIdArrow-impl (f ◆ g)) P₀) ¬p)

  _⋆-PathMon_ : (a b : PathMon 𝒞) -> PathMon 𝒞
  [] ⋆-PathMon b = []
  idp ⋆-PathMon b = b
  arrow f fP ⋆-PathMon [] = []
  arrow f fP ⋆-PathMon idp = arrow f fP
  arrow {a} {b} f fP ⋆-PathMon arrow {b'} {c} g gP with (b ≟-Str b')
  ... | no ¬p = []
  ... | yes p with (c ≟-Str a)
  ... | no c≠a = arrow (rexHom f p ◆ g) (λ a=c -> 𝟘-rec (c≠a (a=c ⁻¹)))
  ... | yes a=c with composeCheckId f g p a=c
  ... | composeNotId fgP = arrow (rexHom f p ◆ g) fgP
  ... | composeIsId x = idp

  infixl 40 _⋆-PathMon_



  private
    lem-10 : ∀{a : PathMon 𝒞} -> idp ⋆-PathMon a ∼ a
    lem-10 {[]} = refl
    lem-10 {idp} = refl
    lem-10 {arrow f fP} = refl

    lem-20 : ∀{a : PathMon 𝒞} -> a ⋆-PathMon idp ∼ a
    lem-20 {[]} = refl
    lem-20 {idp} = refl
    lem-20 {arrow f fP} = refl


{-
    lem-24 : ∀{a b : ⟨ 𝒞 ⟩} -> (p : a ≡-Str b) -> (f : a ⟶ b) -> (P : isIdArrow' f) -> ∀(g : PathMon 𝒞) -> arrow f ⋆-PathMon g ∼ g
    lem-24 p f P [] = refl
    lem-24 refl-StrId f P idp = incl (ι-RST (idp (P refl-StrId)))
    lem-24 {a} {b} p f P (arrow f₁) with (a ≟-Str b)
    ... | yes refl-StrId with (f ≟-∼ id)
    ... | yes p₁ = refl
    ... | no ¬p = let P' = P refl-StrId
                  in 𝟘-rec (¬p P')
    lem-24 {a} {b} p f P (arrow f₁) | no ¬p = 𝟘-rec (¬p p)

    lem-25 : ∀{a : ⟨ 𝒞 ⟩} -> (f : a ⟶ a) -> (f ∼ id) -> ∀(g : PathMon 𝒞) -> arrow f ⋆-PathMon g ∼ g
    lem-25 f p g = lem-24 refl-StrId f
                   (λ q -> let P₀ : refl-StrId ≡-Str q
                               P₀ = isset-Str _ _
                           in transport-Str (cong-Str (λ ξ -> isIdArrow ξ f) P₀) p)
                   g
-}

    lem-30 : ∀{a b c : PathMon 𝒞} -> (a ⋆-PathMon b) ⋆-PathMon c ∼ a ⋆-PathMon (b ⋆-PathMon c)
    lem-30 {[]} {b} {c} = refl
    lem-30 {idp} {b} {c} = refl
    lem-30 {arrow f fP} {[]} {c} = refl
    lem-30 {arrow f fP} {idp} {c} = refl
    lem-30 {arrow {a} {b} f fP} {arrow {b'} {c} g gP} {[]} with (b ≟-Str b')
    ... | no ¬p = refl
    ... | yes p with (c ≟-Str a)
    ... | no ¬p2 = refl
    ... | yes p2 with (composeCheckId f g p p2)
    ... | composeNotId x = refl
    ... | composeIsId x = refl
    lem-30 {arrow {a} {b} f fP} {arrow {b'} {c} g gP} {idp} with (b ≟-Str b')
    ... | no ¬p = refl
    ... | yes p with (c ≟-Str a)
    ... | no ¬p2 = refl
    ... | yes p2 with (composeCheckId f g p p2)
    ... | composeNotId x = refl
    ... | composeIsId x = refl
    lem-30 {arrow {a} {b} f fP} {arrow {b'} {c} g gP} {arrow {c'} {d} h hP} with (b ≟-Str b') | (c ≟-Str c')
    lem-30 {arrow {a} {b} f fP} {arrow {b'} {c} g gP} {arrow {c'} {d} h hP} | no ¬p | no ¬p₁ = refl
    lem-30 {arrow {a} {b} f fP} {arrow {b'} {c} g gP} {arrow {c'} {d} h hP} | no ¬p | yes p with (d ≟-Str b')
    ... | no ¬p₁ with (b ≟-Str b')
    ... | yes b=b' = 𝟘-rec (¬p b=b')
    ... | no ¬p₂ = refl
    lem-30 {arrow {a} {b} f fP} {arrow {b'} {c} g gP} {arrow {c'} {d} h hP} | no ¬p | yes p | yes p3 with composeCheckId g h p p3
    ... | composeNotId x = {!!}
    ... | composeIsId x = {!!}
    lem-30 {arrow {a} {b} f fP} {arrow {b'} {c} g gP} {arrow {c'} {d} h hP} | yes p | no ¬p = {!!}
    lem-30 {arrow {a} {b} f fP} {arrow {b'} {c} g gP} {arrow {c'} {d} h hP} | yes p | yes p₁ = {!!}


{-
    ... | yes refl-StrId with (f ≟-∼ id)
    ... | yes p = refl
    ... | no ¬p with (a ≟-Str b')
    ... | yes p = refl
    ... | no ¬p₁ = refl
    lem-30 {arrow {a} {b} f} {arrow {b'} {c} g} {[]} | no ¬p with (b ≟-Str b')
    ... | yes p = refl
    ... | no ¬p₁ = refl
    lem-30 {arrow {a} {b} f} {arrow {b'} {c} g} {idp} with (a ≟-Str b)
    ... | yes refl-StrId with (f ≟-∼ id)
    ... | yes p = refl
    ... | no ¬p with (a ≟-Str b')
    ... | yes p = refl
    ... | no ¬p₁ = refl
    lem-30 {arrow {a} {b} f} {arrow {b'} {c} g} {idp} | no ¬p with (b ≟-Str b')
    ... | yes p = refl
    ... | no ¬p₁ = refl
    lem-30 {arrow {a} {b} f} {arrow {b'} {c} g} {arrow {c'} {d} h} with (a ≟-Str b) | (b' ≟-Str c)
    ... | yes refl-StrId | yes refl-StrId with (f ≟-∼ id) | (g ≟-∼ id)
    ... | yes p0 | yes p1 = lem-25 g p1 (arrow h) ∙ lem-25 f p0 (arrow h) ⁻¹
    ... | yes p0 | no ¬p with (b' ≟-Str c')
    ... | no ¬p₁ = {!!}
    ... | yes p2 with (b' ≟-Str b') | (a ≟-Str a)
    ... | no ¬p3 | _ = {!!}
    ... | yes p3 | no p4 = {!!}
    ... | yes p3 | yes p4 = {!!}
    lem-30 {arrow {a} {b} f} {arrow {b'} {c} g} {arrow h} | yes refl-StrId | yes refl-StrId | no ¬p | yes p = {!!}
    lem-30 {arrow {a} {b} f} {arrow {b'} {c} g} {arrow h} | yes refl-StrId | yes refl-StrId | no ¬p | no ¬p₁ = {!!}
    lem-30 {arrow {a} {.a} f} {arrow {b'} {c} g} {arrow f₁} | yes refl-StrId | no ¬p = {!!}
    lem-30 {arrow {a} {b} f} {arrow {b'} {c} g} {arrow f₁} | no ¬p | yes p = {!!}
    lem-30 {arrow {a} {b} f} {arrow {b'} {c} g} {arrow f₁} | no ¬p | no ¬p₁ = {!!}


-- {[]} with (b ≟-Str b')
--     ... | yes refl-StrId = refl
--     ... | no ¬p = refl
--     lem-30 {arrow {a} {b} f} {arrow {b'} {c} g} {idp} with (b ≟-Str b')
--     ... | yes refl-StrId = refl
--     ... | no ¬p = refl
--     lem-30 {arrow {a} {b} f} {arrow {b'} {c} g} {arrow {c'} {d} f₁} with (b ≟-Str b') | (c ≟-Str c')
--     lem-30 {arrow {a} {b} f} {arrow {b'} {c} g} {arrow {c'} {d} f₁} | yes p0 | yes q0 with (b ≟-Str b') | (c ≟-Str c')
--     ... | yes p1 | no ¬q = 𝟘-rec (¬q q0)
--     ... | no ¬p | Y = 𝟘-rec (¬p p0)
--     ... | yes p1 | yes q1 with isset-Str p0 p1 | isset-Str q0 q1
--     ... | refl-StrId | refl-StrId with p0 | q0
--     ... | refl-StrId | refl-StrId = incl (ι-RST (arrow assoc-l-◆))
--     lem-30 {arrow {a} {b} f} {arrow {b'} {c} g} {arrow {c'} {d} f₁} | yes refl-StrId | no ¬p with (c ≟-Str c')
--     ... | yes p = 𝟘-rec (¬p p)
--     ... | no ¬p₁ = refl
--     lem-30 {arrow {a} {b} f} {arrow {b'} {c} g} {arrow {c'} {d} f₁} | no ¬p | yes refl-StrId with (b ≟-Str b')
--     ... | yes p = 𝟘-rec (¬p p)
--     ... | no ¬p₁ = refl
--     lem-30 {arrow {a} {b} f} {arrow {b'} {c} g} {arrow {c'} {d} f₁} | no ¬p | no ¬p₁ = refl

{-
    lem-35 : ∀{a0 b0 a1 b1 : PathMon 𝒞} -> (a0 ∼-PathMon a1) -> (b0 ∼-PathMon b1) -> (a0 ⋆-PathMon b0) ∼ (a1 ⋆-PathMon b1)
    lem-35 (idp {a} {f} x) (idp {b} {g} x₁) with (a ≟-Str b)
    ... | yes p = {!!}
    ... | no ¬p = {!!}
    lem-35 (idp x) (arrow p) = {!!}
    lem-35 (arrow p) q = {!!}

    lem-40 : ∀{a0 b0 a1 b1 : PathMon 𝒞} -> (a0 ∼ a1) -> (b0 ∼ b1) -> (a0 ⋆-PathMon b0) ∼ (a1 ⋆-PathMon b1)
    lem-40 {a0} {b0} {a1} {b1} (incl (ι-RST x)) q = {!!}
    lem-40 {a0} {b0} {.a0} {b1} (incl refl-RST) q = {!!}
    lem-40 {a0} {b0} {a1} {b1} (incl (sym-RST p)) q = {!!}
    lem-40 {a0} {b0} {a1} {b1} (incl (p ∙-RST p₁)) q = {!!}


  instance
    isMonoid:PathMon : isMonoid ′(PathMon 𝒞)′
    isMonoid._⋆_ isMonoid:PathMon = _⋆-PathMon_
    isMonoid.◌ isMonoid:PathMon = idp
    isMonoid.unit-l-⋆ isMonoid:PathMon = lem-10
    isMonoid.unit-r-⋆ isMonoid:PathMon = lem-20
    isMonoid.assoc-l-⋆ isMonoid:PathMon {a} {b} {c} = lem-30 {a} {b} {c}
    isMonoid.assoc-r-⋆ isMonoid:PathMon {a} {b} {c} = lem-30 {a} {b} {c} ⁻¹
    isMonoid._`cong-⋆`_ isMonoid:PathMon = lem-40


-}
-}
