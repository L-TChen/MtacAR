{-# OPTIONS -v mtac:100 #-}
module Mtac.Example.Tauto where
open import Prelude
open import Reflection.Extended
open import Mtac

{-# TERMINATING #-}
propTauto : (P : Set) → ○ P
propTauto P =
  try lookupContext P
  finally
    (mcase P of
      ∣ ⊤                           ⇒ ⦇ tt ⦈
      ∣ p ∶ Set , q ∶ Set , (p × q) ⇒ ⦇ propTauto p , propTauto q ⦈
      ∣ p ∶ Set , q ∶ Set , (p ⊎ q) ⇒
        try      ⦇ inj₁ (propTauto _) ⦈
        finally  ⦇ inj₂ (propTauto _) ⦈
      ∣ p ∶ _ ,  p                  ⇒ throw NotFound
    end) 

solve : ℕ → ⊤ → ⊥ ⊎ ℕ × (⊤ ⊎ List ℕ) × ⊤
solve n tt =  Proof propTauto _ ∎ 
