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
      ∣ ⊤                       ⇒ ⦇ tt ⦈
      ∣ p ∶ _ , q ∶ _ , p × q ⇒ ⦇ prop-tauto p , prop-tauto q ⦈
      ∣ p ∶ _ , q ∶ _ , p ⊎ q ⇒
        try      ⦇ inj₁ (prop-tauto _) ⦈
        finally  ⦇ inj₂ (prop-tauto _) ⦈
      ∣ p ∶ Set , q ∶ Set , (p → q) ⇒ ?
      ∣ p ∶ _ ,  p              ⇒ throw NotFound
    end) 
{-
solve : Set → ℕ → ⊤ → ⊥ ⊎ ℕ × (⊤ ⊎ List ℕ) × ⊤
solve A n tt =  Proof prop-tauto _ ∎ 
-}
