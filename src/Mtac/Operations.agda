{-# OPTIONS --safe --without-K #-}

module Mtac.Operations where

open import Prelude
open import Reflection.Extended

open import Mtac.Core

mdebugPrint : ℕ → ErrorParts → ○ ⊤
mdebugPrint n = liftTC ∘ print n

mprint : ErrorParts → ○ ⊤
mprint errs = mdebugPrint 10 errs

------------------------------------------------------------------------
-- Declare a (meta)variable of the given type

mvar : (A : Set ℓ) → ○ A
mvar A = ◎ quoteTC A >>= newMeta >>= return ∘ term

isMvar : A → ○ Bool
isMvar a = liftTC $ isMeta a

------------------------------------------------------------------------
private
  check : Term → (Term × Term) → TC Tac
  check `A (`B , `b) = do
    `A =′ `B
    return $ term `b

  lookup : (A : Set ℓ) → List (Term × Term) → ○ A
  lookup A cxt = ◎ quoteTC A >>= λ `A →
    asum (check `A <$> cxt) <|> return (failed "lookup" `A)

lookupContext : (A : Set ℓ) → ○ A
lookupContext A = liftTC ⦇ (from 0) getContext ⦈ >>= lookup A
  where
    from : ℕ → Args Type → List (Term × Term)
    from n []                 = []
    from n ((arg i `A) ∷ `AS) =
      (`A , var₀ n) ∷ from (1 + n) `AS
