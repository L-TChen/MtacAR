{-# OPTIONS -v mtac:100 --type-in-type #-}
module Mtac.Example.Tauto where
open import Prelude
open import Reflection.Extended
open import Mtac

{-# TERMINATING #-}
propTauto : (P : Set) → ○ P
propTauto P =
  try lookupContext P finally
    (mcase P of
      ∣ ⊤                           ⇒ ` tt `
      ∣ p ∶ Set ▻ q ∶ Set ▻ (p × q) ⇒ ⦇ propTauto p , propTauto q ⦈
      ∣ p ▻ q ▻ (p ⊎ q)             ⇒
        try     ⦇ inj₁ (propTauto p) ⦈
        finally ⦇ inj₂ (propTauto q) ⦈
      ∣ p ∶ Set ▻ p                 ⇒ throw NotFound
      end)

solve : ℕ → ⊥ ⊎ ℕ × (⊤ ⊎ List ℕ) × ⊤
solve n = Proof propTauto _ ∎
