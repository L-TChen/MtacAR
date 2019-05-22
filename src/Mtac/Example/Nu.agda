{-# OPTIONS --allow-unsolved-metas #-}

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
