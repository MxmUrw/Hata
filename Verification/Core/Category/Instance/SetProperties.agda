
{-# OPTIONS --cubical --allow-unsolved-metas --no-import-sorts #-}

module Verification.Core.Category.Instance.SetProperties where

open import Verification.Conventions
open import Verification.Core.Category.Definition
open import Verification.Core.Category.Functor
open import Verification.Core.Category.Adjunction
open import Verification.Core.Category.KanLimit.Definition2
-- open import Verification.Core.Category.Limit.Definition
-- open import Verification.Core.Category.Limit.Product
-- open import Verification.Core.Category.Limit.Equalizer
-- open import Verification.Core.Category.Monad
open import Verification.Core.Category.Instance.Type
open import Verification.Core.Category.Instance.Cat
open import Verification.Core.Category.FreeCategory
open import Verification.Core.Category.Quiver
open import Verification.Core.Category.Instance.Set.Definition
open import Verification.Core.Category.Lift
open import Verification.Core.Homotopy.Level


--------------------------------------------------------------------
-- Equalizers

data Pair : 𝒰₀ where
  ₀ ₁ : Pair


data PairHom : Pair -> Pair -> 𝒰₀ where
  arr₀ : PairHom ₀ ₁
  arr₁ : PairHom ₀ ₁

Quiver:Pair : Quiver (many ℓ₀)
⟨ Quiver:Pair ⟩ = Pair
IQuiver.Edge (of Quiver:Pair) = PairHom
-- IQuiver.Edge (of Quiver:Pair) ₀ ₀ = ⊥
-- IQuiver.Edge (of Quiver:Pair) ₀ ₁ = 𝟚-𝒰
-- IQuiver.Edge (of Quiver:Pair) ₁ b = ⊥
IQuiver._≈_ (of Quiver:Pair) = _≡_
IQuiver.IEquivInst (of Quiver:Pair) = IEquiv:Path

Category:Pair = Category:Free (Quiver:Pair)

instance
  ICategory:Pair = of Category:Pair

-- instance
--   Index-Notation:Diagram : ∀{S : Quiver (ℓ₀ , ℓ₀ , ℓ₀)} {X : Category 𝑖} -> Index-Notation ((↑ Category:Free S) ⟶ X)
--                                                                                            (⟨ S ⟩ ×-𝒰 ⟨ S ⟩)
--                                                                                            (IAnything)
--                                                                                            (λ (D , (a , b)) -> Edge {{of S}} a b -> Hom (⟨ D ⟩ (lift a)) (⟨ D ⟩ (lift b)))
--   (Index-Notation:Diagram Index-Notation.⌄ D) (a , b) e = map (lift (some (last e)))


record _=?=-Set_ {A : Set 𝑖} {B : Set 𝑗} (f g : HTypeHom A B) : 𝒰 (𝑖 ､ 𝑗) where
  constructor _,_
  field fst : ⟨ A ⟩
        snd : ⟨ f ⟩ fst ≡ ⟨ g ⟩ fst
        -- {{Set:B}} : IHType 2 ⟨ B ⟩
open _=?=-Set_ public

-- _S,_ : {A : Set 𝑖} {B : Set 𝑗} {f g : HTypeHom A B} -> (a : ⟨ A ⟩) -> (p : ⟨ f ⟩ a ≡ ⟨ g ⟩ a) -> f =?=-Set g
-- _S,_ {B = B} a p = _,_ a p {{of B}}

_Set:=?=-Set_ : {A : Set 𝑖} {B : Set 𝑗} -> (f g : HTypeHom A B) -> Set (𝑖 ､ 𝑗)
⟨ f Set:=?=-Set g ⟩ = f =?=-Set g
of (f Set:=?=-Set g) = {!!}


-- _=?=-Set_ : {A : Set 𝑖} {B : Set 𝑗} -> (f g : HTypeHom A B) -> Set (𝑖 ､ 𝑗)
-- ⟨ f =?=-Set g ⟩ = ∑ λ a -> ⟨ f ⟩ a ≡ ⟨ g ⟩ a
-- IHType.hlevel (of (_=?=-Set_  {A = A} {B} f g)) = isOfHLevelΣ 2 (hlevel {{of A}}) (λ x -> isOfHLevelSuc 1 (hlevel {{of B}} _ _))


byFirst1 : {A : Set 𝑖} {B : Set 𝑗} -> {f g : HTypeHom A B} -> {a b : f =?=-Set g} -> fst a ≡ fst b -> a ≡ b
byFirst1 {A = A}{B}{f}{g}{a}{b} p i = p i , isSet→isSet' (hlevel {{of B}}) (snd a) (snd b) (cong ⟨ f ⟩ (p)) (cong ⟨ g ⟩ (p)) i

-- instance
--   Cast:SigmaEq : ∀{𝑖 𝑗 : 𝔏} {A : Set 𝑖} {B : Set 𝑗} -> {f g : HTypeHom A B} -> {a b : f =?=-Set g} -> Cast (fst a ≡ fst b) IAnything (a ≡ b)
--   Cast.cast Cast:SigmaEq p = byFirst1 p


-- {⟨ f ⟩ (fst a)} {⟨ g ⟩ (fst a)} {⟨ f ⟩ (fst b)} {⟨ g ⟩ (fst b)} ? ? ? ? i
-- byFirst1 {A = A}{B}{f}{g}{a}{b} p i = p i , isSet→isSet' (hlevel {{of B}}) {⟨ f ⟩ (fst a)} {⟨ g ⟩ (fst a)} {⟨ f ⟩ (fst b)} {⟨ g ⟩ (fst b)} ? ? ? ? i

-- byFirst0 : {A : Set 𝑖} {B : Set 𝑗} -> {f g : HTypeHom A B} -> {a : ⟨ A ⟩} -> {b1 b2 : ⟨ f ⟩ a ≡ ⟨ g ⟩ a} -> PathP (λ i -> f =?=-Set g) (a , b1) (a , b2)
-- byFirst0 {B = B} {f} {g} {a} {b1} {b2} i = _ , hlevel {{of B}} _ _ b1 b2 i
-- byFirst1 p = {!!}


-- instance
--   setinstance : ∀{A : 𝒰 𝑖} -> {F : A -> Set 𝑗} -> ∀{a : A} -> ISet (⟨ F a ⟩)
--   setinstance {F = F} {a = a} = of (F a)

byfirst : ∀{A : 𝒰 𝑖} {B : A -> 𝒰 𝑗} -> ∀{a1 : A} -> {b1 : B a1} {b2 : B a1} -> (isOfHLevel 1 (B a1)) -> PathP (λ i -> ∑ λ (a : A) -> B a) (a1 , b1) (a1 , b2)
byfirst {b1 = b1} {b2} lev i = _ , lev b1 b2 i



byfirst2 : ∀{A : 𝒰 𝑖} {B : A -> 𝒰 𝑗} -> ∀{a1 : A} -> {b1 : B a1} {b2 : B a1} -> {{_ : IHType 1 (B a1)}} -> PathP (λ i -> ∑ λ (a : A) -> B a) (a1 , b1) (a1 , b2)
byfirst2 {b1 = b1} {b2} {{lev}} i = _ , (hlevel {{lev}}) b1 b2 i

-- testttt = cong2

funExtSet : ∀{A : Set 𝑖} {B : Set 𝑗} -> {f g : HTypeHom A B} -> (∀(a : ⟨ A ⟩) -> {{_ : IHType 2 ⟨ B ⟩}} -> ⟨ f ⟩ a ≡ ⟨ g ⟩ a) -> HTypeHomEq f g
⟨ funExtSet p ⟩ = λ i x -> p x i
of funExtSet p = record {}

-- explicitArgs : ∀{A : 𝒰 𝑖} {B : 𝒰 𝑗} {C : 𝒰 𝑙} {D : 𝒰 𝑘} -> (f : )

module _ where
  private
    L : Functor (⩚ (↑ Category:Pair ⟶ ⩚ Set 𝑖)) (⩚ (𝟙 ⟶ ⩚ Set 𝑖))
    ⟨ L {𝑖} ⟩ F = free-Diagram-Lift f
      where f : QuiverHom (⩚ ⊤) (ForgetCategory (⩚ Set _))
            ⟨ f ⟩ _ = ((map {{of F}} (↥ ` arr₀ `)) Set:=?=-Set (map {{of F}} (↥ ` arr₁ `)))
              -- where instance _ = of (⟨ F ⟩ (↥ ₀))
              --                _ = of (⟨ F ⟩ (↥ ₁))
            -- ∑ λ (x : ⟨ ⟨ F ⟩ (↥ ₀) ⟩) -> (F ⌄ (₀ , ₁)) ₀ x ≡ (F ⌄ (₀ , ₁)) ₁ x
            IQuiverHom.qmap (of f) e = ⌘ λ x -> x
    IFunctor.map (of L) α = free-Diagram-Nat f (λ {()})
      where f = λ {_ -> ⌘ λ {(x , xp) -> ⟨ ⟨ α ⟩ ⟩ x , let P : ⟨ (⟨ α ⟩ ◆ map _) ⟩ x ≡ ⟨ (⟨ α ⟩ ◆ map _) ⟩ x
                                                           P = ((naturality _ x)) ∙ cong ⟨ ⟨ α ⟩ ⟩ xp ∙ ( (naturality _ x ⁻¹))
                                                           -- P = (cong (λ ξ -> ξ $ x) (naturality _ x)) ∙ cong ⟨ ⟨ α ⟩ ⟩ xp ∙ (cong (λ ξ -> ξ $ x) (naturality _ ⁻¹))
                                                        in P}}
      -- where f = λ {_ (x , xp) -> ⟨ α ⟩ x , let P : ⟨ α ⟩ ◆ map _ ≡ ⟨ α ⟩ ◆ map _
      --                                          P = naturality _ ∙ {!!}
      --                                      in cong (_$ x) P}
    IFunctor.functoriality-id (of L) {a = a} α _ = byFirst1 refl --funExt (λ _ -> byFirst1 refl)
    -- funExt (λ {(x , xp) -> byfirst (targethlevel {{of (map α)}} _ _) }) -- {{of ⟨ a ⟩ (↥ ₁)}}
    -- x , hlevel {{of ⟨ a ⟩ (↥ ₁)}} _ _ _ _ i}) -- ({!!} , {!!})
    IFunctor.functoriality-◆ (of L) {a = a} {b} {c} x _ = byFirst1 refl -- funExt (λ _ -> byFirst1 refl) -- funExt (λ _ -> byfirst (hlevel {{of ⟨ c ⟩ (↥ ₁)}} _ _))
    IFunctor.functoriality-≣ (of L) p _ x = byFirst1 (p _ (fst x))


    𝒫 : ∀{𝑖} -> Category 𝑖
    𝒫 = ↑ Category:Pair

    -- FG = Functor:comp-Cat L (! 𝒫 *)


    ε : ∀(x : (𝒫) ⟶ ` Set 𝑖 `) -> ∀(a : Pair)
        -> (⟨ ⟨ ! 𝒫 * ⟩ (⟨ L ⟩ x) ⟩ (↥ a)) ⟶ ⟨ x ⟩ (↥ a)
    ε x ₀ = ⌘ λ (a , p) -> a
    ε x ₁ = ⌘ λ (a , p) -> ⟨ map {{of x}} (` arr₀ `) ⟩ a -- ((x ⌄ (₀ , ₁)) ₀)⟩ a

    εp : ∀{𝑖} -> ∀(x : 𝒫 ⟶ (⩚ Set 𝑖)) -> ∀{a b : Pair} -> (e : Edge {{of Quiver:Pair}} a b)
        -> ε x a ◆ map (` e `) ≣ map {{of (⟨ ! 𝒫 * ⟩ (⟨ L ⟩ x))}} {a = ↥ a} {b = ↥ b} (` e `) ◆ ε x b
        -- (⟨ ⟨ ! (↑ Category:Pair) * ⟩ (⟨ L ⟩ x) ⟩ (↥ a)) ⟶ ⟨ x ⟩ (↥ a)
    εp x {₀} {₁} arr₀ _ = refl
    εp x {₀} {₁} arr₁ (y , yp) =  let -- P : ? fst (⟨ map {{of x}} (↥ ` ₁ `) ⟩ (y , yp)) ≡ ?
                                      P : (⟨ map {{of x}} (` arr₁ `) ⟩ y) ≡ (⟨ map {{of x}} (` arr₀ `) ⟩ y)
                                      P = yp ⁻¹
                                  in P

    ε' : ∀(x : 𝒫 ⟶ ` Set 𝑖 `) -> Natural (⟨ ! 𝒫 * ⟩ (⟨ L ⟩ x)) x
    ε' x = free-Diagram-Nat (ε x) (εp x)

    -- ε2 : ∀{𝑖 : 𝔏} -> ∀{a b : Pair}
    --     -> ∀(g : Edge a b) -> ∀(x : (↑ Category:Pair) ⟶ (Category:Set 𝑖)) -> ⊤ -- ∀(e : ) -- (⟨ ⟨ ! (↑ Category:Pair) * ⟩ (⟨ L ⟩ x) ⟩ (↥ a)) ⟶ ⟨ x ⟩ (↥ a)
    -- ε2 = {!!}

    η : ∀(x : 𝟙 ⟶ ` Set 𝑖 `) -> ∀(a : ⊤)
        -> ⟨ x ⟩ (↥ a) ⟶ (⟨ ⟨ L ⟩ (⟨ ! 𝒫 * ⟩ x) ⟩ (↥ a))
    η _ = λ _ -> ⌘ λ {a -> (a , refl)}

    η' : ∀(x : 𝟙 ⟶ ` Set 𝑖 `) -> Natural x (⟨ L ⟩ (⟨ ! 𝒫 * ⟩ x))
    η' x = free-Diagram-Nat (η x) (λ {()})


    lem::1 : (! (↑ Category:Pair) *) ⊣ L {𝑖 = 𝑖}
    ⟨ IAdjoint.embed lem::1 ⟩ {x = x} = η' x -- free-Diagram-Nat (η x) 
      -- where f = λ _ -> ⌘ λ {a -> (a , refl)}
      --       fp = λ {()}
    INatural.naturality (of IAdjoint.embed lem::1) f x _ = byFirst1 refl -- funExt (λ {_ -> byFirst1 refl})
    ⟨ IAdjoint.eval lem::1 ⟩ {x = x} = ε' x
    -- free-Diagram-Nat (ε x) (εp x) -- (εp x) --  (λ {{a = ₀} {b = ₁} ₀ -> {!!};
    --                                                           {₀} {₁} ₁ -> ?})
    --   where f = λ {₀ -> (⌘ λ {(a , p) -> a});
    --                ₁ -> (⌘ λ {(a , p) -> ⟨((x ⌄ (₀ , ₁)) ₀)⟩ a})}
            -- fp = ?
    INatural.naturality (of IAdjoint.eval lem::1) α (↥ ₀) _ = refl -- funExt (λ {_ -> byFirst1 refl})
    INatural.naturality (of IAdjoint.eval lem::1) {x = a} {b} α (↥ ₁) (x , xp) =
                           let P : ⟨ ⟨ α ⟩ ⟩ (⟨ map {{of a}} (` arr₀ `) ⟩ x) ≡ ⟨ map {{of b}} (` arr₀ `) ⟩ (⟨ ⟨ α ⟩ ⟩ x)
                               P = naturality {{of α}} (` arr₀ `) x ⁻¹
                            in P
    IAdjoint.reduce-Adj-β lem::1 (↥ ₀) _ = refl
    IAdjoint.reduce-Adj-β lem::1 {a = a} (↥ ₁) x = functoriality-id {{of a}} x
    IAdjoint.reduce-Adj-η lem::1 (↥ tt) _ = byFirst1 refl -- funExt (λ _ -> byFirst1 refl)


-- Evaluating reduce-β by hand...
-- even though agda can show it...
      -- let -- P : ⟨ (map {{of ! 𝒫 *}} (η' a) ◆ ε' (⟨ ! 𝒫 * ⟩ a)) ⟩ {↥ ₁} ≣ id
      --     -- P = {!!}
      --     -- Q : ⟨ map {{of ! 𝒫 *}} (η' a) ⟩ {↥ ₁} ◆ ⟨ ε' (⟨ ! 𝒫 * ⟩ a) ⟩ {↥ ₁} ≣ id
      --     -- Q = {!!}

      --     -- Q' : ⟨ ⟨ map {{of ! 𝒫 *}} (η' a) ⟩ {↥ ₁} ◆ ⟨ ε' (⟨ ! 𝒫 * ⟩ a) ⟩ {↥ ₁} ⟩ ≡ id {{of Category:𝒰 _}}
      --     -- Q' = {!!}

      --     -- Q'' : ⟨ ⟨ map {{of ! 𝒫 *}} (η' a) ⟩ {↥ ₁} ⟩ ◆ ⟨ ⟨ ε' (⟨ ! 𝒫 * ⟩ a) ⟩ {↥ ₁} ⟩ ≡ id {{of Category:𝒰 _}}
      --     -- Q'' = {!!}

      --     -- Q''' : ∀ x -> ⟨ ⟨ ε' (⟨ ! 𝒫 * ⟩ a) ⟩ {↥ ₁} ⟩ (⟨ ⟨ map {{of ! 𝒫 *}} (η' a) ⟩ {↥ ₁} ⟩ x) ≡ x
      --     -- Q''' = {!!}

      --     -- Q'''' : ∀ x -> ⟨ map {{of (⟨ ! 𝒫 * ⟩ a)}} ` arr₀ ` ⟩ (fst (⟨ ⟨ map {{of ! 𝒫 *}} (η' a) ⟩ {↥ ₁} ⟩ x)) ≡ x
      --     -- Q'''' = {!!}

      --     -- Q''''' : ∀ x -> ⟨ map {{of (⟨ ! 𝒫 * ⟩ a)}} ` arr₀ ` ⟩ (fst (⟨ ⟨ η' a ⟩ { ⟨ (! 𝒫) ⟩ (↥ ₁)} ⟩ x)) ≡ x
      --     -- Q''''' = {!!}

      --     -- Q'''''' : ∀ x -> ⟨ map {{of (⟨ ! 𝒫 * ⟩ a)}} ` arr₀ ` ⟩ (fst (⟨ ⟨ η' a ⟩ { (↥ tt)} ⟩ x)) ≡ x
      --     -- Q'''''' = {!!}

      --     -- Q''''''' : ∀ x -> ⟨ map {{of (! 𝒫 ◇ a)}} ` arr₀ ` ⟩ (x) ≡ x
      --     -- Q''''''' = {!!}

      --     -- Q'''''''' : ∀ x -> ⟨ map {{of a}} (map {{of ! 𝒫}} ` arr₀ `) ⟩ (x) ≡ x
      --     -- Q'''''''' = {!!}

      --     -- Q''''''''' : ∀ x -> ⟨ map {{of a}} (id {{of 𝟙}}) ⟩ (x) ≡ x
      --     -- Q''''''''' = {!!}
      --     aa : ℕ
      --     aa = 1

      -- in functoriality-id {{of a}}



