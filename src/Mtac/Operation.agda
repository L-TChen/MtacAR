{-# OPTIONS --safe --without-K #-}

module Mtac.Operation where

open import Prelude
open import Reflection.Extended
  renaming (getContext to getContextTC)

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
isMvar a = liftTC $ caseM quoteTC a of λ where
    (meta x args) → return true
    _             → return false

_≟_ : A → B → ○ Bool
a ≟ b = (◎ do
  (`a , `b) ← ⦇ quoteTC a , quoteTC b ⦈
  `a =′ `b
  return○′ true) <|> return false

-- dangerous
coe : ○ A → ○ B
coe ma = ◎ (toTC ma)

------------------------------------------------------------------------
private
  from : ℕ → Args Type → List (Term × Term)
  from n []                 = []
  from n ((arg i `A) ∷ `AS) =
    (`A , var₀ n) ∷ from (1 + n) `AS

  check : Term → (Term × Term) → TC Tac
  check `A (`B , `b) = do
    `A =′ `B
    return $ term `b

lookup : (A : Set ℓ) → List (Term × Term) → ○ A
lookup A cxt = ◎ quoteTC A >>= λ `A →
  asum (check `A <$> cxt) <|> return (failed "lookup" `A)

getContext : ○ List (Term × Term)
getContext = liftTC $ from 0 <$> getContextTC

lookupContext : (A : Set ℓ) → ○ A
lookupContext A = getContext >>= lookup A
