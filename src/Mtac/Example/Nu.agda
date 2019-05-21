{-# OPTIONS --allow-unsolved-metas #-}

module Mtac.Example.Nu where

open import Prelude.Core
open import Mtac

any : ○ A
any {A = A} = ν x ∶ A ⇒ ⦇ x ⦈

runAny : A
runAny = {! run any !}

withoutNu : ℕ → ○ ℕ
withoutNu = λ y → ν x ∶ ℕ ⇒ (try ⦇ x ⦈ finally ⦇ 42 ⦈)

runWithoutNu : ℕ → ℕ
runWithoutNu n = run (withoutNu n) 

