{-# OPTIONS -v mtac:100 --allow-unsolved-meta  #-}
module Mtac.Examples.Tauto where

open import Prelude
open import Reflection.Extended

open import Mtac

{-# TERMINATING #-}
prop-tauto : {P : Set} → ○ P
prop-tauto {P} =
  mcase P of
     ∣ ⊤                       ⇒   ⦇ tt ⦈
     ∣ P ∶ _ , Q ∶ _ , P × Q   ⇒   ⦇ prop-tauto , prop-tauto ⦈
     ∣ P ∶ _ , Q ∶ _ , P ⊎ Q   ⇒   ⦇ inj₁ prop-tauto | inj₂ prop-tauto ⦈
     ∣ P ∶ _ , P               ⇒   ⦇⦈
  end

-- A simple first-order tautology prover.

{-# TERMINATING #-}
tauto : (P : Set ℓ) → ○ P
tauto {ℓ} P = mcase P of
     ∣ P ∶ Set ℓ , Q ∶ Set ℓ , P × Q   ⇒ ⦇ tauto P , tauto Q ⦈
     ∣ P ∶ Set ℓ , Q ∶ Set ℓ , P ⊎ Q   ⇒ ⦇ inj₁ (tauto P) | inj₂ (tauto Q) ⦈
     ∣ A ∶ _ , P ∶ (A → Set) , (∀ a → P a)  ⇒ (ν y ∶ A ⇒ ƛ y ⇒ tauto (P y))
     ∣ A ∶ Set ℓ , Q ∶ (A → Set ℓ) , Σ A Q  ⇒ (do
       x ← mvar A
       r ← (tauto (Q x))
       ifM isMvar x then ⦇⦈ else ⦇ (Σ A Q ∋ (x , r))  ⦈ )
     ∣ A ∶ _ , x ∶ A , x ≡ x  ⇒ ⦇ refl ⦈
     ∣ P ⇒ (lookupContext P)
     end

trivial₁ : (n : ℕ) → ⊥ ⊎ (n ≡ n) × (Σ _ λ n → n ≡ 0)
trivial₁ = run (tauto _)


-- -- -- trivial₂ : ℕ → List ℕ → ℕ -- see issue agda/agda#3831
-- -- -- trivial₂ = {! run (tauto _) !}
