{-
  let vα = lookup-Listᴰ Q k∍i
      α = lookup-Listᴰ² Γ k∍i
      σᵤ₀ : μs ⟶ μs ⊔ vα
      σᵤ₀ = ι₀

      α₀ = α ⇃[ id ]⇂

      Γ₀ = Γ ⇃[ ι₀ ]⇂ᶜ

      Γ<Γ₀ : Γ <Γ Γ₀
      Γ<Γ₀ = record { fst = σᵤ₀ ; snd = refl-≡ }

      lem-1 : lookup-Listᴰ² (Γ ⇃[ ι₀ ]⇂ᶜ) k∍i ⇃[ ⦗ id , ι₁ ⦘ ]⇂ ≡ lookup-Listᴰ² Γ k∍i ⇃[ id ]⇂
      lem-1 = trans-Path (§-ℒHMCtx.prop-2 {Γ = Γ} k∍i ι₀ ι₁) (lookup-Listᴰ² Γ k∍i ⇃[≀ §-ℒHMTypes.prop-1 ⁻¹ ≀]⇂)

  in right ((μs / vα ⊩ Γ , α₀ , reflexive , var k∍i ι₁ lem-1)

           -- now we have to prove that this is the "initial" such typing instance
           , λ {(μs₁ / να₁ ⊩ Γ₁ , α₁ , Γ<Γ₁ , var {Γ = Γ₁'} _ ρ Γp) →

               -- given another instance, which has to use `var` to prove the typing

                let σᵤ₁ : μs ⟶ μs₁
                    σᵤ₁ = Γ<Γ₁ .fst


                    σᵤ₁-ty : lookup-Listᴰ Q k∍i ⟶ μs₁ ⊔ να₁
                    σᵤ₁-ty = ρ

                    lem-4 : Γ ⇃[ σᵤ₁ ◆ ι₀ ]⇂ᶜ ≡ Γ₁ ⇃[ ι₀ ]⇂ᶜ
                    lem-4 = Γ ⇃[ σᵤ₁ ◆ ι₀ ]⇂ᶜ      ⟨ sym-Path functoriality-◆-⇃[]⇂-CtxFor ⟩-≡
                            Γ ⇃[ σᵤ₁ ]⇂ᶜ ⇃[ ι₀ ]⇂ᶜ ⟨ cong _⇃[ ι₀ ]⇂ᶜ (Γ<Γ₁ .snd) ⟩-≡
                            Γ₁ ⇃[ ι₀ ]⇂ᶜ           ∎-≡


                    lem-5 : lookup-Listᴰ² Γ k∍i ⇃[ id ]⇂ ⇃[ ⦗ σᵤ₁ ◆ ι₀ , ρ ⦘ ]⇂ ≡ α₁
                    lem-5 = lookup-Listᴰ² Γ k∍i ⇃[ id ]⇂ ⇃[ ⦗ σᵤ₁ ◆ ι₀ , ρ ⦘ ]⇂

                            ⟨ cong _⇃[ ⦗ σᵤ₁ ◆ ι₀ , ρ ⦘ ]⇂ (functoriality-id-⇃[]⇂ {τ = lookup-Listᴰ² Γ k∍i}) ⟩-≡
                            lookup-Listᴰ² Γ k∍i ⇃[ ⦗ σᵤ₁ ◆ ι₀ , ρ ⦘ ]⇂

                            ⟨ sym-Path (§-ℒHMCtx.prop-2 {Γ = Γ} k∍i (σᵤ₁ ◆ ι₀) (ρ)) ⟩-≡

                            lookup-Listᴰ² (Γ ⇃[ σᵤ₁ ◆ ι₀ ]⇂ᶜ) k∍i ⇃[ ⦗ id , ρ ⦘ ]⇂

                            ⟨ cong (λ ξ -> lookup-Listᴰ² ξ k∍i ⇃[ ⦗ id , ρ ⦘ ]⇂) lem-4 ⟩-≡

                            lookup-Listᴰ² (Γ₁ ⇃[ ι₀ ]⇂ᶜ) k∍i ⇃[ ⦗ id , ρ ⦘ ]⇂

                            ⟨ Γp ⟩-≡

                            α₁

                            ∎-≡

                in record { tiSubₐ = σᵤ₁ ; tiSubₓ = ρ ; typProof = lem-5 ; subProof = unit-l-◆ }

               })
-}
