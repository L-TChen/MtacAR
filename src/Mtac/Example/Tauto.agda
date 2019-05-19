{-# OPTIONS --type-in-type #-}

module Mtac.Example.Tauto where

open import Prelude
open import Reflection.Extended

open import Mtac

{-# TERMINATING #-}
tauto : (P : Set) → ○ P
tauto P = do
  mprint [ strErr "\n--------------STARTING----------------" ]
  mcase P of
    ∣ ⊤                 ⇒ return tt
    ∣ p :> q :> (p × q) ⇒ ⦇ tauto p , tauto q ⦈
    ∣ p :> q :> (p ⊎ q) ⇒
      try     (tauto p >>= return ∘ inj₁)
      finally (tauto q >>= return ∘ inj₂)
    ∣ p :> p            ⇒ throw NotFound
    end
