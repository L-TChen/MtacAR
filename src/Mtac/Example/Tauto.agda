{-# OPTIONS -v mtac:100 --type-in-type #-}

module Mtac.Example.Tauto where

open import Prelude
open import Reflection.Extended

open import Mtac

{-# TERMINATING #-}
tauto : (P : Set) → ○ P
tauto P = do
  mprint [ strErr "\n--------------STARTING----------------" ]
  mcase P of
    ∣ [ ⊤ ]⇒ return tt
    ∣ p ▻ q ▻ [ p × q ]⇒ ⦇ tauto p , tauto q ⦈
    ∣ p ▻ q ▻ [ p ⊎ q ]⇒
      try     ⦇ inj₁ (tauto p) ⦈
      finally ⦇ inj₂ (tauto q) ⦈
    ∣ p ▻         [ p ]⇒ throw NotFound
    end

prop1 : ○ ⊤ × (⊥ ⊎ ⊤)
prop1 = tauto _

solve-prop1 : ⊤ × (⊥ ⊎ ⊤)
solve-prop1 = {!run (tauto $ ⊤ × ⊤)!}
