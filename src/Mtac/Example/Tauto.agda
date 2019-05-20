{-# OPTIONS -v mtac:100 --type-in-type #-}

module Mtac.Example.Tauto where

open import Prelude
open import Reflection.Extended

open import Mtac

{-# TERMINATING #-}
tauto : (P : Set) → ○ P
tauto P = do
  --mprint [ strErr "\n--------------STARTING----------------" ]
  try lookupContext P finally
    (mcase P of
      ∣ [ ⊤ ]⇒ ` tt `
      ∣ p ▻ q ▻ [ p × q ]⇒ ⦇ tauto p , tauto q ⦈
      ∣ p ▻ q ▻ [ p ⊎ q ]⇒
        try     ⦇ inj₁ (tauto p) ⦈
        finally ⦇ inj₂ (tauto q) ⦈
      ∣ p ▻         [ p ]⇒ throw NotFound
      end)

solve : ℕ → ℕ × ⊤
solve n = {!run (tauto $ ℕ × ⊤ )!}
