{-# OPTIONS -v mtac:100 --allow-unsolved-meta #-}
module Mtac.Examples.Tauto where

open import Prelude
open import Reflection.Extended

open import Mtac

{-# TERMINATING #-}
prop-tauto : {P : Set} → ○ P
prop-tauto {P} = mcase P of
     ∣ ⊤                     ⇒ ⦇ tt ⦈
     ∣ P ∶ _ , Q ∶ _ , P × Q ⇒ ⦇ prop-tauto , prop-tauto ⦈
     ∣ P ∶ _ , Q ∶ _ , P ⊎ Q ⇒ ⦇ inj₁ prop-tauto | inj₂ prop-tauto ⦈
     ∣ A ∶ _ , P ∶ (A → Set) , (∀ a → P a) ⇒
       (ν y ∶ A ⇒ ƛ y ⇒ prop-tauto)
     ∣ A ∶ Set , Q ∶ (A → Set) , Σ A Q ⇒ (do
       x ← mvar A
       bind ○_ (prop-tauto {Q x}) λ r → ⦇ if (isMvar x) then ⦇⦈ else ⦇ (x , r) ⦈ ⦈)
     {-(do
       x ← mvar A
       _>>=_ {○_} (prop-tauto {Q x}) λ r → ⦇ if (isMvar x) then ⦇⦈ else ⦇ (x , r) ⦈ ⦈ )-}
     ∣ A ∶ _ , x ∶ A , x ≡ x ⇒ ⦇ refl ⦈
     ∣ P ∶ _ , P             ⇒ lookupContext P
   end

solve : (n : ℕ) → ⊥ ⊎ ℕ × ⊤ × (n ≡ n)
solve = run prop-tauto 


f : Σ ℕ λ n → n ≡ 3
f = {!!} -- run prop-tauto

