{-# OPTIONS -v mtac:100 --type-in-type #-}

module Mtac.Example.Tauto where

open import Prelude
open import Reflection.Extended

open import Mtac

{-# TERMINATING #-}
tauto : (P : Set) → ○ P
tauto P =
  try lookupContext P finally
    (mcase P of
      ∣ ⊤ ⇒ ` tt `
      ∣ p ∶ Set ▻ q ∶ Set ▻ (p × q) ⇒ ⦇ tauto p , tauto q ⦈
      ∣ p ▻ q ▻ (p ⊎ q) ⇒
        try     ⦇ inj₁ (tauto p) ⦈
        finally ⦇ inj₂ (tauto q) ⦈
      ∣ p ∶ Set ▻ p ⇒ throw NotFound
      end)

--solve : ℕ → ℕ × ⊤ 
--solve n = run (tauto $ ℕ × ⊤ )
