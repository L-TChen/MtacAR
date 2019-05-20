module Mtac.Operation where

open import Prelude 
open import Reflection.Extended

open import Mtac.Core

mdebugPrint : ℕ → ErrorParts → ○ ⊤
mdebugPrint n = liftTC ∘ print n

mprint : ErrorParts → ○ ⊤
mprint errs = mdebugPrint 2 errs

`_` : A → ○ A
`_` = returnR

isEvar : {A : Set ℓ} → A → ○ Bool
isEvar {A} a = ◎ do
  (meta _ _) ← quoteTC a where _ → term <$> quoteTC false
  ⦇ term (quoteTC true) ⦈

------------------------------------------------------------------------
-- Dyns is a list of pairs (`A, `t) such that t : A. Due to level
-- restriction, they are encoded as Term.
private 
  countFrom : ℕ → Args Type → List (Term × Term)
  countFrom n []                     = []
  countFrom n ((arg i `A) ∷ `AS) =
    (`A , var n []) ∷ countFrom (1 + n) `AS

  check : Term → Term × Term → TC Tac
  check `A (`B , `b) = do
    `A =′ `B
    return $ term `b

lookupContext : (A : Set ℓ) → ○ A
lookupContext A = (◎ do
  `A  ← quoteTC A
  cxt ← countFrom 0 <$> getContext 
  asum (map {T = List} (check `A) cxt))
  
  <|> throw NotFound
