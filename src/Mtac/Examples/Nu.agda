{-# OPTIONS --allow-unsolved-metas -v mtac:100 #-}

module Mtac.Examples.Nu where

open import Prelude
open import Mtac

solveAny : (A : Set) → ○ A
solveAny A = ν x ∶ A ⇒ ⦇ x ⦈

Magic : ⊥
Magic = {! run (ν x ∶ ⊥ ⇒ ⦇ x ⦈) !} -- Uncaught exception: The result contains a local name

NoNu : ℕ
NoNu = Proof
  try (ν x ∶ ℕ ⇒ return x) catch (λ where
    LocalName → return 42
    _         → return 24)
  ∎

Abs : ○ (ℕ → ℕ)
Abs = ν y ∶ ℕ ⇒ ƛ y ⇒ ⦇ y ⦈

