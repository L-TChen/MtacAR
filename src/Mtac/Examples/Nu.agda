{-# OPTIONS --allow-unsolved-metas -v mtac:10 #-}

module Mtac.Examples.Nu where

open import Prelude
open import Reflection.Extended hiding (Abs)

open import Mtac
open import Mtac.Binders


solveAny : (A : Set) → ○ A
solveAny A = ν x ∶ A ⇒ ⦇ x ⦈

Magic : ⊥
Magic = {! run (ν x ∶ ⊥ ⇒ ⦇ x ⦈) !} -- Local names cannot escape their context

NoNu : ℕ
NoNu = Proof
  try (ν x ∶ ℕ ⇒ return x) catch (λ where
    (LocalName `t) → return 42
    _              → return 24)
  ∎

Abs-test : (ℕ → List ℕ → ℕ)
Abs-test = run (ν x ∶ ℕ ⇒ mabs x "x"
  =<< (ν y ∶ List ℕ ⇒ mabs y "y" x))

