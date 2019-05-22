{-# OPTIONS -v mtac:100 --type-in-type #-}

module Mtac.Example.Tauto where

open import Prelude
open import Reflection.Extended

open import Mtac

{-# TERMINATING #-}
propTauto : {P : Set} → ○ P
propTauto {P = P} =
  try lookupContext P finally
    (mcase P of
      ∣ ⊤                           ⇒ ` tt `
      ∣ p ∶ Set ▻ q ∶ Set ▻ (p × q) ⇒ ⦇ propTauto , propTauto  ⦈
      ∣ p ▻ q ▻ (p ⊎ q)             ⇒
        try     ⦇ inj₁ propTauto ⦈
        finally ⦇ inj₂ propTauto ⦈
      ∣ p ∶ Set ▻ p                 ⇒ throw NotFound
      end)

solve : ℕ → ℕ × ℕ × ℕ × ⊤ 
solve n = {! Proof propTauto ∎ !}
