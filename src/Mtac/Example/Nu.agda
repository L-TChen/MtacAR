{-# OPTIONS --allow-unsolved-metas #-}

module Mtac.Example.Nu where

open import Prelude.Core
open import Mtac

solveAny : ○ A
solveAny {A = A} = ν x ∶ A ⇒ ⦇ x ⦈

runAny : A
runAny = {!run solveAny!}

withoutNu : ○ ℕ
withoutNu = ν x ∶ ℕ ⇒ (try lookupContext ℕ finally (return $ fst (x , 42)))

runWithoutNu : ℕ → ℕ
runWithoutNu n = run withoutNu

