{-# OPTIONS -v mtac:100 --allow-unsolved-meta #-}
module Mtac.Examples.Tauto where
open import Prelude
open import Reflection.Extended

open import Mtac

{-# TERMINATING #-}
prop-tauto : {P : Set} → ○ P
prop-tauto {P = P} = lookupContext P <|>
  (mcase P of
     ∣ ⊤                     ⇒ ⦇ tt ⦈
     ∣ P ∶ _ , Q ∶ _ , P × Q ⇒ ⦇ prop-tauto , prop-tauto ⦈
     ∣ P ∶ _ , Q ∶ _ , P ⊎ Q ⇒ ⦇ inj₁ prop-tauto | inj₂ prop-tauto ⦈
     ∣ P ∶ _ , P             ⇒ ⦇⦈ 
   end)
      
solve : ℕ → ⊥ ⊎ ⊥ ⊎ ℕ × ℕ × ⊤
solve n = run prop-tauto

