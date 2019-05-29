{-# OPTIONS -v mtac:100 #-}
module Mtac.Example.Tauto where
open import Prelude
open import Reflection.Extended

open import Mtac

{-# TERMINATING #-}
prop-tauto : (P : Set) → ○ P
prop-tauto P =
  try lookupContext P
  finally
    (mcase P of
      ∣ ⊤                     ⇒ ⦇ tt ⦈
      ∣ P ∶ _ , Q ∶ _ , P × Q ⇒ ⦇ prop-tauto P , prop-tauto Q ⦈
      ∣ P ∶ _ , Q ∶ _ , P ⊎ Q ⇒
        try      ⦇ inj₁ (prop-tauto _) ⦈
        finally  ⦇ inj₂ (prop-tauto _) ⦈
      ∣ A ∶ _ , P ∶ (A → Set) , (∀ x → P x) ⇒
        (ν y ∶ A ⇒ ƛ y ⇒ prop-tauto (P y))
      ∣ P ∶ Set ,  P              ⇒ throw NotFound
    end) 
{-
solve : ⊤ × ⊤
solve = run (prop-tauto _) 

-}
