{-# OPTIONS -v mtac:100 --allow-unsolved-meta  #-}
module Mtac.Examples.Tauto where

open import Prelude
open import Reflection.Extended

open import Mtac

-- A simple first-order tautology prover.

{-# TERMINATING #-}
tauto : {P : Set ℓ} → ○ P
tauto {ℓ} {P} = mcase P ∶ (λ τ → τ) of
     ∣ P ∶ Set ℓ , Q ∶ Set ℓ , P × Q  ⇒ ⦇ tauto , tauto ⦈
     ∣ P ∶ Set ℓ , Q ∶ Set ℓ , P ⊎ Q  ⇒ ⦇ inj₁ tauto | inj₂ tauto ⦈
     ∣ A ∶ _ , P ∶ (A → Set) , (∀ a → P a)  ⇒ (ν y ∶ A ⇒ ƛ y ⇒ tauto)
     ∣ A ∶ Set ℓ , Q ∶ (A → Set ℓ) , Σ A Q  ⇒ (do
       x ← mvar A
       bind ○_ (tauto {ℓ} {Q x}) λ r →
         ifM isMvar x then ⦇⦈ else ⦇ (x , r) ⦈ ) -- why instance argument cannot solve this?
     ∣ A ∶ _ , x ∶ A , x ≡ x  ⇒ ⦇ refl ⦈
     ∣ P ∶ _ , P              ⇒ lookupContext _ end

solve : (n : ℕ) → ⊥ ⊎ (n ≡ n) × (Σ _ λ n → n ≡ 0)
solve = run tauto
