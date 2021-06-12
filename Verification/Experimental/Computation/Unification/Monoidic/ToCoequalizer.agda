
module Verification.Experimental.Theory.Computation.Unification.Monoidic.ToCoequalizer where

open import Verification.Conventions

open import Verification.Experimental.Category.Std.Category.Definition
open import Verification.Experimental.Category.Std.Limit.Specific.Coequalizer
open import Verification.Experimental.Category.Std.Category.As.Monoid
open import Verification.Experimental.Set.Setoid.Definition
open import Verification.Experimental.Set.Decidable
open import Verification.Experimental.Set.Discrete
open import Verification.Experimental.Data.Prop.Everything
open import Verification.Experimental.Data.Sum.Definition
open import Verification.Experimental.Order.Preorder
open import Verification.Experimental.Order.Lattice
open import Verification.Experimental.Theory.Computation.Unification.Definition
open import Verification.Experimental.Theory.Computation.Unification.Monoidic.PrincipalFamilyCat2
open import Verification.Experimental.Algebra.Monoid.Definition
open import Verification.Experimental.Algebra.MonoidWithZero.Definition
open import Verification.Experimental.Algebra.MonoidWithZero.Ideal
open import Verification.Experimental.Algebra.MonoidAction.Definition


module _ {𝒞 : Category 𝑖} {{_ : isDiscrete ⟨ 𝒞 ⟩}} {{_ : isSet-Str ⟨ 𝒞 ⟩}} where
  module _ {a b : ⟨ 𝒞 ⟩} (f g : a ⟶ b) where
    private
      f' g' : PathMon 𝒞
      f' = arrow f
      g' = arrow g
      -- J : Ideal-r ′ PathMon 𝒞 ′
      -- J = ′(CoeqSolutions f' g')′
      All : Ideal-r ′ PathMon 𝒞 ′
      All = ′ ⊤ ′
      II : Ideal-r ′ PathMon 𝒞 ′
      II = ′(CoeqSolutions f' g')′

    module by-Principal-Unification {G : Submonoid ′ PathMon 𝒞 ′} (P : isPrincipal/⁺-r G ′(CoeqSolutions f' g')′) where
      proof : isDecidable (hasCoequalizer f g)
      proof = {!!}
      {-
      proof with split-+-Str (zeroOrCancel-r {{_:>_.Proof2> P}})
      ... | left (rep=[] , snd₁) = left (λ X ->
              let rr = rep {{_:>_.Proof1> P}}
                  h : b ⟶ ⟨ X ⟩
                  h = π-Coeq
                  h' : PathMon 𝒞
                  h' = arrow h
                  P₀ : f' ⋆ h' ∼ g' ⋆ h'
                  P₀ = functoriality-arrow f h ⁻¹ ∙ incl (arrow ∼-Coeq) ∙ functoriality-arrow g h
                  P₁ : ⟨ CoeqSolutions f' g' h' ⟩
                  P₁ = incl P₀
                  P₂ : ⟨ ⟨ rr ↷-Ide All ⟩ h' ⟩
                  P₂ = ⟨ ⟨ principal-r ⟩ ⟩ P₁
                  incl (x , xP , xQ) = P₂

                  P₃ : h' ∼ rr ⋆ x
                  P₃ = xQ

                  P₄ : h' ∼ ◍
                  P₄ = P₃ ∙ (rep=[] ≀⋆≀ refl)

                  P₅ : h' ∼ ◍ -> 𝟘-𝒰
                  P₅ = λ ()

              in P₅ P₄
            )
      ... | just ((rep≁◍ , cancelRep) , Q₀) = case-PathMon (rep' ′(CoeqSolutions f' g')′) of
        (λ (p : rep' II ∼ [])  -> 𝟘-rec (rep≁◍ p))
        (λ (p : rep' II ∼ idp) ->
          let P₀ : ⟨ CoeqSolutions f' g' (rep' II) ⟩
              P₀ = Principal-r::rep-in-ideal

              P₁ : ⟨ CoeqSolutions f' g' idp ⟩
              P₁ = transp-Subsetoid {{_}} {{isSubsetoid:CoeqSolutions}} p P₀

              P₂ : arrow f ⋆ idp ∼ arrow g ⋆ idp
              P₂ = ⟨ P₁ ⟩

              P₃ : arrow f ∼ arrow g
              P₃ = unit-r-⋆ ⁻¹ ∙ P₂ ∙ unit-r-⋆

              P₄ : f ∼ g
              P₄ = PathMon-arrow-path-inv f g refl refl ⟨ P₃ ⟩

              X : Coeq-ExUniq f g b
              X = record
                    { π-CoeqEU = id
                    ; ∼-CoeqEU = unit-r-◆ ∙ P₄ ∙ unit-r-◆ ⁻¹
                    ; elim-CoeqEU = λ h _ -> h
                    ; reduce-CoeqEU = λ _ _ -> unit-l-◆
                    ; unique-CoeqEU = λ i j p -> unit-l-◆ ⁻¹ ∙ p ∙ unit-l-◆
                    }

          in right (′ b ′ {{by-CoeqEU-Coeq X}})
        )

        (λ {b'} {c} {i} -> λ {rep=i -> case-Decision (b ≟-Str b') of

          -- if b ≠ b', then there cannot exist a coequalizer
          (λ (b≢b' : b ≢-Str b') ->

            -- We assume that we have a coeq
            left (λ X ->
              let rr = rep {{_:>_.Proof1> P}}
                  h : b ⟶ ⟨ X ⟩
                  h = π-Coeq
                  h' : PathMon 𝒞
                  h' = arrow h
                  P₀ : f' ⋆ h' ∼ g' ⋆ h'
                  P₀ = functoriality-arrow f h ⁻¹ ∙ incl (arrow ∼-Coeq) ∙ functoriality-arrow g h
                  P₁ : ⟨ CoeqSolutions f' g' h' ⟩
                  P₁ = incl P₀
                  P₂ : ⟨ ⟨ rr ↷-Ide All ⟩ h' ⟩
                  P₂ = ⟨ ⟨ principal-r {{_:>_.Proof1> P}} ⟩ ⟩ P₁
                  incl (x , xP , xQ) = P₂

                  -- We derive that then an x must exist such that our coeq h' factors through rr (since rr is the representing element)
                  P₃ : h' ∼ rr ⋆ x
                  P₃ = xQ

                  P₄ : h' ∼ (arrow i) ⋆ x
                  P₄ = P₃ ∙ (rep=i ≀⋆≀ refl)

                  -- We now look at the different cases for what x might be
                  P₅ = case-PathMon x of

                        (λ (q : x ∼ []) ->
                          let Q₁ : (h' ∼ []) -> _
                              Q₁ = λ {()}
                              Q₂ : (arrow i ⋆ x ∼ [])
                              Q₂ = (incl (arrow {𝒞 = 𝒞} refl) ≀⋆≀ q)
                          in Q₁ (P₄ ∙ Q₂))

                        (λ (q : x ∼ idp) ->
                          let Q₁ : (h' ∼ arrow i)
                              Q₁ = P₄ ∙ (incl (arrow {𝒞 = 𝒞} refl) ≀⋆≀ q) ∙ unit-r-⋆
                              Q₂ : h' ∼ (arrow i) -> b ≡-Str b'
                              Q₂ = λ {(incl (arrow _)) -> refl}
                          in 𝟘-rec (b≢b' (Q₂ Q₁))
                        )

                        (λ {x0} {x1} {x'} (q : x ∼ arrow x') ->
                          case-Decision (c ≟-Str x0) of

                            -- if the composition i ◆ x' is not well formed, i.e., c≠x0, then we have i◆x' = []
                            (λ {c≢x0 ->
                              let P₆ : h' ∼ []
                                  P₆ = P₄ ∙ (refl ≀⋆≀ q) ∙ PathMon-non-matching-arrows c≢x0 i x'
                                  P₇ : (h' ∼ []) -> _
                                  P₇ = λ {()}
                              in P₇ P₆
                            })

                            -- if the composition i ◆ x' is well formed
                            (λ {refl-StrId ->
                              let P₈ : h' ∼ (arrow (i ◆ x'))
                                  P₈ = P₄ ∙ (refl ≀⋆≀ q) ∙ functoriality-arrow i x' ⁻¹
                                  P₉ : h' ∼ (arrow (i ◆ x')) -> b ≡-Str b'
                                  P₉ = λ {(incl (arrow _)) -> refl}
                              in 𝟘-rec (b≢b' (P₉ P₈))
                            })
                          )
              in P₅
          ))

          -- finally, if b = b', we can show that i is a coequalizer
          (λ {refl-StrId ->
            let π : b ⟶ c
                π = i

                -- we know that rep is in the CoeqSolutions ideal
                P₀ : ⟨ (CoeqSolutions f' g') (rep' II) ⟩
                P₀ = Principal-r::rep-in-ideal

                -- thus, since rep is actually the arrow i, it is also in this ideal
                P₁ : ⟨ (CoeqSolutions f' g') (arrow i) ⟩
                P₁ = transp-Subsetoid rep=i P₀

                -- by definition of this ideal, this means that f⋆i ∼ g⋆i
                P₂ : (arrow f ⋆ arrow i) ∼ (arrow g ⋆ arrow i)
                P₂ = ⟨ P₁ ⟩

                -- we do know that the codomain of f/g and the domain of i match, thus, we can use functoriality of the arrow to
                -- get the same statement on the level of categories
                -- This finishes the proof that f ◆ π ∼ g ◆ π
                P₃ : f ◆ i ∼ g ◆ i
                P₃ =
                  let q : arrow {𝒞 = 𝒞} (f ◆ i) ∼ arrow (g ◆ i)
                      q = functoriality-arrow f i ∙ P₂ ∙ functoriality-arrow g i ⁻¹
                      q' : arrow {𝒞 = 𝒞} (f ◆ i) ∼ arrow (g ◆ i) -> f ◆ i ∼ g ◆ i
                      q' = λ {(incl p) -> PathMon-arrow-path-inv (f ◆ i) (g ◆ i) refl refl p}
                      -- q' = λ {(incl (arrow p)) -> p}
                  in q' q


                -- 2. We now have to show that given any other h which makes f and g equal, we get a hom from c.
                P₄ : ∀{d : ⟨ 𝒞 ⟩} -> (h : b ⟶ d) -> (f ◆ h ∼ g ◆ h) -> (∑ λ (j : c ⟶ d) -> (i ◆ j ∼ h))
                P₄ {d} h hP =
                  let h' = arrow h
                      rr = rep' II
                      -- we show that h is in the ideal
                      Q₀ : ⟨ CoeqSolutions f' g' h' ⟩
                      Q₀ = incl (functoriality-arrow f h ⁻¹ ∙ incl (arrow hP) ∙ functoriality-arrow g h)

                      -- this means that it is also element of the "factoring ideal"/principal ideal
                      Q₂ : ⟨ ⟨ rr ↷-Ide All ⟩ h' ⟩
                      Q₂ = ⟨ ⟨ principal-r {{_:>_.Proof1> P}} ⟩ ⟩ Q₀
                      incl (x , xP , xQ) = Q₂

                      -- i.e., we get
                      Q₃ : h' ∼ rr ⋆ x
                      Q₃ = xQ

                      Q₄ : h' ∼ (arrow i) ⋆ x
                      Q₄ = Q₃ ∙ (rep=i ≀⋆≀ refl)

                      -- we look at the different options for x
                      Q₅ = case-PathMon x of

                          -- the case that x is [] can clearly not happen, for then the result of (arrow i ⋆ x) would not be an arrow
                          (λ (q : x ∼ []) ->
                            let R₁ : (h' ∼ []) -> _
                                R₁ = λ {()}
                                R₂ : (arrow i ⋆ x ∼ [])
                                R₂ = (incl (arrow {𝒞 = 𝒞} refl) ≀⋆≀ q)
                            in R₁ (Q₄ ∙ R₂))

                          -- if x is idp, then h' is simply i
                          (λ (q : x ∼ idp) ->
                            let R₁ : h' ∼ arrow i
                                R₁ = Q₄ ∙ (incl (arrow {𝒞 = 𝒞} refl) ≀⋆≀ q) ∙ unit-r-⋆
                                R₂ : d ≡-Str c
                                R₂ = PathMon-arrow-path-matching-codom h i ⟨ R₁ ⟩
                                R₃ : d ≡-Str c -> _
                                R₃ = λ {refl-StrId ->
                                  let R₄ : h ∼ i
                                      R₄ = PathMon-arrow-path-inv h i refl refl ⟨ R₁ ⟩
                                      R₅ : i ◆ id ∼ h
                                      R₅ = unit-r-◆ ∙ R₄ ⁻¹
                                  in id , R₅
                                  }
                            in R₃ R₂
                          )

                          -- the most interesting case is where x is really an arrow
                          (λ {x0} {x1} {x'} (q : x ∼ arrow x') ->
                            -- but we still have to check whether the domain of x' fits to the codomain of π
                            case-Decision (c ≟-Str x0) of

                              -- if the composition i ◆ x' is not well formed, i.e., c≠x0, then we have i◆x' = []
                              (λ {c≢x0 ->
                                  let P₆ : h' ∼ []
                                      P₆ = Q₄ ∙ (refl ≀⋆≀ q) ∙ PathMon-non-matching-arrows c≢x0 i x'
                                      P₇ : (h' ∼ []) -> _
                                      P₇ = λ {()}
                                  in P₇ P₆
                              })

                              -- if the composition i ◆ x' is well formed
                              (λ {refl-StrId ->
                                -- and, further, we also have to check whether x1 = d
                                case-Decision (d ≟-Str x1) of

                                  -- the case that they are not equal cannot happen, since this would mean that R₀ shouldn't hold
                                  (λ d≢x1 ->
                                    let R₀ : h' ∼ (arrow (i ◆ x'))
                                        R₀ = Q₄ ∙ (refl ≀⋆≀ q) ∙ functoriality-arrow i x' ⁻¹
                                        R₁ : d ≡-Str x1
                                        R₁ = PathMon-arrow-path-matching-codom h (i ◆ x') ⟨ R₀ ⟩
                                    in 𝟘-rec (d≢x1 R₁)
                                  )

                                  -- if x1 = d
                                  (λ {refl-StrId ->
                                    -- then we can return x'. But actually, we also want to show that the β rules hold for π, so we have to do...
                                    let -- we show the β rule
                                        R₀ : arrow (i ◆ x') ∼ arrow h
                                        R₀ = functoriality-arrow i x' ∙ (refl ≀⋆≀ q ⁻¹) ∙ Q₄ ⁻¹
                                        R₁ : (i ◆ x') ∼ h
                                        R₁ = PathMon-arrow-path-inv (i ◆ x') h refl refl ⟨ R₀ ⟩

                                    in x' , R₁
                                  })
                              }))
                  in Q₅

                -- the η rule, i.e., uniqueness of the coeq
                P₅ : ∀{d : ⟨ 𝒞 ⟩} -> (v w : c ⟶ d) -> (i ◆ v ∼ i ◆ w) -> v ∼ w
                P₅ v w P =
                  let rr = rep' II
                      Q₀ : rr ⋆ arrow v ∼ rr ⋆ arrow w
                      Q₀ = (rep=i ≀⋆≀ refl) ∙ functoriality-arrow i v ⁻¹ ∙ (incl (arrow P)) ∙ functoriality-arrow i w ∙ (rep=i ⁻¹ ≀⋆≀ refl)
                      Q₁ : arrow v ∼ arrow w
                      Q₁ = cancelRep Q₀
                      Q₂ : v ∼ w
                      Q₂ = PathMon-arrow-path-inv v w refl refl ⟨ Q₁ ⟩
                  in Q₂


                -- we build the coequalizer structure
                X : Coeq-ExUniq f g c
                X = record
                      { π-CoeqEU = π
                      ; ∼-CoeqEU = P₃
                      ; elim-CoeqEU = λ h p -> P₄ h p .fst
                      ; reduce-CoeqEU = λ h p -> P₄ h p .snd
                      ; unique-CoeqEU = P₅
                      }
            in right (′ c ′ {{by-CoeqEU-Coeq X}})
          })
          })

-}



