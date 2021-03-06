
module Verification.Core.Meta.Structure4 where

open import Verification.Conventions hiding (âª_â« ; Structure ; â²_â²)
-- open import Verification.Core.Category.Definition
-- open import Verification.Core.Category.Instance.Set.Definition
open import Verification.Core.Order.Preorder renaming (IPreorder to isPreorder)


-- record Structure {A : ð° ð} (P : A -> ð° ð) : ð° (ð â ð) where
--   constructor str
--   field â¨_â© : A
--         {of_} : P â¨_â©
--         -- of_ : P â¨_â©


  -- infixr 2 of_

record âi_ {A : ð° ð} (B : A -> ð° ð) : ð° (ð ï½¤ ð) where
  instance constructor makeâi
  -- field overlap {{ifst}} : A
  field {ifst} : A
  field overlap {{isnd}} : B (ifst)
open âi_ {{...}} public

record hasU (A : ð° ð) ð ð : ð° (ð âº ï½¤ ð âº) where
  field getU : ð° ð
  field getP : getU -> ð° ð

open hasU public

record hasU2 {A : ð° ð} (P : A -> ð° ð) ð ð : ð° (ð ï½¤ ð ï½¤ ð âº ï½¤ ð âº) where
  field getU2 : A -> ð° ð
        getP2 : â{a : A} -> getU2 a -> ð° ð
        reconstruct : â{a} -> (â getP2 {a}) -> P a
open hasU2 public

_on2_ : {A : ð° ð} (P : A -> ð° ð) {{U : hasU2 P ð ð}} -> (a : A) -> {{_ : getU2 U a}} -> ð° _
_on2_ P {{U}} a = getP2 U {a = a} it

-- _on_ : (UU : ð° ð) {{U : hasU UU ð ð}} -> (a : getU U) -> ð° _
-- _on_ UU {{U}} a = getP U a

record _:>_ {A : ð° ð} (P : A -> ð° ð) {{U : hasU2 P ðâ ðâ}} (Q : (a : A) -> {{_ : P a}} -> ð° ð)
            (a : A) : ð° (ð ï½¤ ð ï½¤ ð ï½¤ ðâ ï½¤ ðâ) where
  constructor make:>
  field {âª_â«} : getU2 U a
  field {Proof1} : getP2 U âª_â«
  field overlap {{Proof2}} : Q a {{reconstruct U (âª_â« , Proof1)}}

infixl 50 _:>_

record From (A : ð° ð) (a : A) : ð°â where

record isAnything {A : ð° ð} (a : A) : ð°â where

instance
  From:Any : â{A : ð° ð} {a : A} -> From A a
  From:Any = record {}

instance
  isAnything:anything : {A : ð° ð} {a : A} -> isAnything a
  isAnything:anything = record {}

instance
  hasU2:From : â{A : ð° ð} -> hasU2 (From A) _ _
  getU2 (hasU2:From {A = A}) = From A
  getP2 (hasU2:From {A = A}) = isAnything
  reconstruct (hasU2:From {A = A}) x = record {}


instance
  hasU2:> : {A : ð° ð} {P : A -> ð° ð} {{U : hasU2 P ðâ ðâ}} {Q : (a : A) -> {{_ : P a}} -> ð° ð} -> hasU2 (P :> Q) _ _
  getU2 (hasU2:> {A = A} {P} â¦ U â¦ {Q}) = getU2 U
  getP2 (hasU2:> {A = A} {P} â¦ U â¦ {Q}) a = âi Î» (p1 : getP2 U a) -> Q _ {{reconstruct U (_ , p1)}}
  reconstruct (hasU2:> {A = A} {P} â¦ U â¦ {Q}) (a , pa) = make:> {âª_â« = a} {pa .ifst} {{pa .isnd}}

-- {UU : ð° ð} {{U : hasU2 UU ð ð}} {P : UU -> ð° ð} -> hasU (UU :& P) _ _

-- instance
--   hasU:âi : â{A : ð° ð} {P : A -> ð° ð} -> hasU (âi P) _ _
--   getU (hasU:âi {A = A} {P}) = A
--   getP (hasU:âi {A = A} {P}) = P


{-
record _:>>_ {A : ð° ð} {P0 : A -> ð° ðâ} (P : (a : A) -> {{_ : P0 a}} -> ð° ð) (Q : (a : A) -> {{_ : (P0 :> P) a}} -> ð° ð) (a : A) {{_ : P0 a}} : ð° (ð ï½¤ ð ï½¤ ð) where
  field {{Proof1}} : P a
  field {{Proof2}} : Q a

infixl 50 _:>>_


record âi_ {A : ð° ð} (B : A -> ð° ð) : ð° (ð ï½¤ ð) where
  instance constructor makeâi
  -- field overlap {{ifst}} : A
  field {ifst} : A
  field overlap {{isnd}} : B (ifst)
open âi_ {{...}} public

record âp (ð : ð) {ð ð : ð} {A : ð° ð} {Q : A -> ð° ð} (B : (a : A) -> {{_ : Q a}} -> ð° ð) : ð° (ð ï½¤ ð) where
  instance constructor makeâp
  -- field overlap {{ifst}} : A
  -- field {ifst} : A
  -- field overlap {{isnd}} : B (ifst)
open âp {{...}} public




-}


record Structure {A : ð° ð} (P : A -> ð° ð) {{U : hasU2 P ð ð}} : ð° (ð ï½¤ ð ï½¤ ð) where
  constructor â²_â²
  field â¨_â© : A
        {Proof3-useless} : getU2 U â¨_â©
        {Proof3} : getP2 U Proof3-useless

open Structure public

-- â²_â² : {A : ð° ð} {P : A -> ð° ð} -> (a : A) -> {{_ : P a}} -> Structure P
-- â²_â² a {{X}} = str a {_} {X}

-- â²_â² : {A : ð° ð} {P : A -> ð° ð} -> (a : A) -> {{_ : P a}} -> Structure P
-- â²_â² a {{X}} = str a {_} {X}



instance
  hasU:Structure : â{A : ð° ð} {P : A -> ð° ð} {{_ : hasU2 P ð ð}} -> hasU (Structure P) _ _
  getU (hasU:Structure {A = A} {P}) = A
  getP (hasU:Structure {A = A} {P}) = P

_on_ : (UU : ð° ð) {{U : hasU UU ð ð}} -> (a : getU U) -> ð° _
_on_ UU {{U}} a = getP U a

is_ : (UU : ð° ð) {{U : hasU UU ð ð}} -> (a : getU U) -> ð° _
is_ UU {{U}} a = getP U a

infixl 100 is_
{-

record _:,_ {U : ð° ð} {R : U -> ð° ðâ} (P : (a : U) -> {{_ : R a}} -> ð° ð) (Q : (a : U) -> {{_ : R a}} -> ð° ðâ) (a : U) {{_ : R a}} : ð° (ð ï½¤ ðâ) where
  constructor make,
  field overlap {{Proof1}} : P a
  field overlap {{Proof2}} : Q a

infixr 80 _:,_


--------------------------------------------------
-- Testcase
-}


-- record hasU2 {A : ð° ð} (P : A -> ð° ð) ð ð : ð° (ð ï½¤ ð ï½¤ ð âº ï½¤ ð âº) where

module TEST where
  private

    record isTypoid ð A {{_ : From (ð° ð) A}} : ð° (ð ï½¤ ð âº) where
      field _â¼_ : A -> A -> ð° ð
    open isTypoid {{...}} public

    -- Typoid : â(ð : ð ^ 2) -> ð° _
    -- Typoid ð = Structure (isType (ð â 0) :> isTypoid (ð â 1))

    Typoid : (ð : ð ^ 2) -> ð° _
    Typoid ð = Structure (From (ð° (ð â 0)) :> isTypoid (ð â 1))

    -- record isMonoid (A : ð° _) {{_ : Typoid ð on A}} : ð° (ð) where
    record isMonoid (A : ð° _) {{_ : (From (ð° ð) :> isTypoid ð) A }} : ð° (ð) where
      field _â_ : A -> A -> A
    -- record isMonoid A {{_ : (isType ð :> isTypoid) A}} : ð° (ð) where
    open isMonoid {{...}} public

    -- strOf : {A : ð° ð} {P : A -> ð° ð} {{_ : hasU2 P ð ð}} -> {a : A} -> (_ : )

    Monoid : â(ð : ð ^ 2) -> ð° _
    Monoid ð = Structure (From (ð° (ð â 0)) :> isTypoid (ð â 1) :> isMonoid)
    -- ((is Typoid ð :> isMonoid) on2_)

{-
    -- âp (ð âº) {ð = ð} {Q = isTypoid} isMonoid
    -}

    record isCommutative A {{_ : (is Monoid ð) A}} : ð° (ð ï½¤ ð) where
      field comm-â : â{a b : A} -> (a â b) â¼ (b â a)
    open isCommutative {{...}} public

{-
    record isGroup A {{_ : Monoid ð on A}} : ð° ð where
      field â¡_ : A -> A

{-
    Group : â(ð) -> ð° _
    Group ð = Structure ((Monoid ð on_) :> isGroup)


    record isSemiring (A : ð° _) {{_ : (is Monoid ð :> isCommutative) A}} : ð° ð where
      field _â_ : A -> A -> A

    Semiring : â(ð) -> ð° _
    Semiring ð = Structure (_ :> isSemiring {ð = ð})

    record isRing (A : ð° _) {{_ : (is Monoid ð :> ((isCommutative :>> isSemiring) :, isGroup)) A}} : ð° ð where

-}
    record isTypoidHom {A B} {{_ : Typoid ð on A}} {{_ : Typoid ð on B}} f {{_ : (From (A -> B)) f}} : ð° (ð ï½¤ ð) where
      field preserves-â¼ : â{a b : A} -> a â¼ b -> f a â¼ f b

    TypoidHom : (A : Typoid ð) (B : Typoid ð) -> ð° _
    TypoidHom A B = Structure (_ :> isTypoidHom {{of A}} {{of B}})

    -- record isTypoidHom (A : Typoid ð) (B : Typoid ð) (f : â¨ A â© -> â¨ B â©) : ð° (ð ï½¤ ð) where
    --   field preserves-â¼ : â{a b : â¨ A â©} -> a â¼ b -> f a â¼ f b

    -- TypoidHom : (A : Typoid ð) (B : Typoid ð) -> ð° _
    -- TypoidHom A B = Structure (isTypoidHom A B)

    record isMonoidHom {A B} {{_ : Monoid ð on A}} {{_ : Monoid ð on B}} (f : A -> B) {{_ : (_ :> isTypoidHom) f}} : ð° (ð ï½¤ ð) where

    -- record isMonoidHom (A : Monoid ð) (B : Monoid ð) (f : â¨ A â© -> â¨ B â©) {{_ : TypoidHom (â² â¨ A â© â²) (â² â¨ B â© â²) on f}} : ð° (ð ï½¤ ð) where

    MonoidHom : (A : Monoid ð) (B : Monoid ð) -> ð° _
    MonoidHom A B = Structure (_ :> isMonoidHom {{of A}} {{of B}})

{-
{-


    record isGroupHom {A B} {{_ : Group ð on A}} {{_ : Group ð on B}} (f : A -> B) {{_ : (_ :> isMonoidHom) f}} : ð° (ð ï½¤ ð) where

-}
    -- record isMonoidHom (A : Monoid ð) (B : Monoid ð) f {{_ : TypoidHom (â â¨ A â©) (â â¨ B â©) on f}} : ð° (ð ï½¤ ð) where

    -- record isCommutative (A : ð° ð) {{_ : (isTypoid :> isMonoid) A}} : ð° ð where


-}

-}

