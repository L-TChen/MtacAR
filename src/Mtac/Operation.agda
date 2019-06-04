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
-- Declare a (meta)variable of the given type

mvar : (A : Set ℓ) → ○ A
mvar A = ◎ quoteTC A >>= newMeta >>= return ∘ term

isMvar : {A : Set ℓ} → A → ○ Bool
isMvar {A} a = liftTC $ quoteTC a >>= reduce >>= λ where
  (meta _ _) → return true
  _          → return false

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

lookup : (A : Set ℓ) → List (Term × Term) → ○ A
lookup A cxt = ◎ quoteTC A >>= λ `A → 
  asum (check `A <$> cxt) <|> return (failed "lookup" `A)
  
lookupContext : (A : Set ℓ) → ○ A
lookupContext A = (liftTC $ countFrom 0 <$> getContext) >>= lookup A
