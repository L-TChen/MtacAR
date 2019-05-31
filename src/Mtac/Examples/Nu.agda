{-# OPTIONS --allow-unsolved-metas -v mtac:100 #-}

module Mtac.Example.Nu where

open import Prelude.Core
open import Mtac

solveAny : ○ A
solveAny {A = A} = ν x ∶ A ⇒ ⦇ x ⦈

runAny : A
runAny = {!run solveAny!}

NoNu : ℕ
NoNu = Proof
  try (ν x ∶ ℕ ⇒ return x) finally return 42
  ∎

Abs : ○ (ℕ → _)
Abs = ν y ∶ ℕ ⇒ ƛ y ⇒ return y

