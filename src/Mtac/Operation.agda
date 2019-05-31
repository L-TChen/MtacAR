{-# OPTIONS --safe --without-K #-}

module Mtac.Operation where

open import Prelude.Core
open import Reflection.Extended

open import Mtac.Core

mdebugPrint : ℕ → ErrorParts → ○ ⊤
mdebugPrint n = liftTC ∘ print n

mprint : ErrorParts → ○ ⊤
mprint errs = mdebugPrint 2 errs

------------------------------------------------------------------------
private
  countFrom : ℕ → Args Type → List (Term × Term)
  countFrom n []                 = []
  countFrom n ((arg i `A) ∷ `AS) =
    (`A , var₀ n) ∷ countFrom (1 + n) `AS

  check : Term → (Term × Term) → TC Tac
  check `A (`B , `b) = do
    `A =′ `B
    return $ term `b

lookupContext : (A : Set ℓ) → ○ A
lookupContext A = ◎ do
  `A  ← quoteTC A
  cxt ← countFrom 0 <$> getContext
  asum (map {T = List} (check `A) cxt) <|> return (failure $ strErr "lookup context failed" ∷ [])

------------------------------------------------------------------------
-- Declare a (meta)variable of the given type

mvar : (A : Set ℓ) → ○ A
mvar A = ◎ quoteTC A >>= newMeta >>= return○′

isMvar : {A : Set ℓ} → A → ○ Bool
isMvar {A} a = liftTC $ quoteTC a >>= reduce >>= λ
  { (meta _ _) → return true
  ; _          → return false
  }
