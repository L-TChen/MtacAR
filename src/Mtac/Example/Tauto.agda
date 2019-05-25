{-# OPTIONS -v mtac:100 #-}
module Mtac.Example.Tauto where
open import Prelude
open import Reflection.Extended
open import Mtac

{-# TERMINATING #-}
propTauto : ∀ (P : Set) → ○ P
propTauto P =
  try lookupContext P finally
    (mcase P of
      ∣ [ ⊤ ]⇒ ⦇ tt ⦈
      ∣ p ▻ q ▻ [ p × q ]⇒ ⦇ propTauto p , propTauto q ⦈
      ∣ p ▻ q ▻ [ p ⊎ q ]⇒
        try     ⦇ inj₁ (propTauto _) ⦈
        finally ⦇ inj₂ (propTauto _) ⦈
      ∣ p ▻ [ p ]⇒ throw NotFound
    end) 

solve : ℕ → ⊥ ⊎ ℕ × (⊤ ⊎ List ℕ) × ⊤
solve n = Proof
  propTauto _
  ∎
