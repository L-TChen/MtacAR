{-# OPTIONS -v mtac:100 #-}
module Mtac.Examples.Tauto where
open import Prelude
open import Reflection.Extended

open import Mtac

{-# TERMINATING #-}
prop-tauto : (P : Set) → ○ P
prop-tauto P = lookupContext P
  <|> (mcase P of
       ∣ ⊤                     ⇒ ⦇ tt ⦈
       ∣ P ∶ _ , Q ∶ _ , P × Q ⇒ ⦇ prop-tauto P , prop-tauto Q ⦈
       ∣ P ∶ _ , Q ∶ _ , P ⊎ Q ⇒
         ⦇ inj₁ (prop-tauto P) ⦈ <|> ⦇ inj₂ (prop-tauto Q) ⦈
       ∣ A ∶ _ , P ∶ (A → Set) , (∀ x → P x) ⇒
         (ν y ∶ A ⇒ ƛ y ⇒ prop-tauto (P y))
       ∣ P ∶ Set ,  P              ⇒ azero
      end) 

solve : ℕ → ℕ × ℕ  
solve n = {!run (prop-tauto _)!} -- run (prop-tauto _) 

