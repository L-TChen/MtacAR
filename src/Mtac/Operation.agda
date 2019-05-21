{-# OPTIONS --allow-unsolved-metas #-}

module Mtac.Operation where

open import Prelude.Core
open import Reflection.Extended

open import Mtac.Core

mdebugPrint : ℕ → ErrorParts → ○ ⊤
mdebugPrint n = liftTC ∘ print n

mprint : ErrorParts → ○ ⊤
mprint errs = mdebugPrint 2 errs

`_` : A → ○ A
`_` = return

------------------------------------------------------------------------
-- Dyns is a list of pairs (`A, `t) such that t : A. Due to level
-- restriction, they are encoded as Term.
private 
  countFrom : ℕ → Args Type → List (Term × Term)
  countFrom n []                     = []
  countFrom n ((arg i `A) ∷ `AS) =
    (`A , var n []) ∷ countFrom (1 + n) `AS

  check : Term → (Term × Term) → TC Tac
  check `A (`B , `b) = do
    `A =′ `B
    return $ term `b

lookupContext : (A : Set ℓ) → ○ A
lookupContext A = (◎ do
  `A  ← quoteTC A
  cxt ← countFrom 0 <$> getContext 
  asum (map {T = List} (check `A) cxt))
  
  <|> throw NotFound

------------------------------------------------------------------------
-- Declare a (meta)variable of the given type

mvar : (A : Set ℓ) → ○ A
mvar A = ◎ quoteTC A >>= newMeta >>= return○′

isMvar : {A : Set ℓ} → A → ○ Bool
isMvar {A} a = liftTC $ quoteTC a >>= reduce >>= λ
  { (meta _ _) → return true
  ; _          → return false
  }

-- how to report error message? 
nu : (A : Set ℓ) → (A → ○ B) → ○ B
nu A f = ◎ quoteTC A >>= λ `A → extendContext (vArg `A ) do
  x ← unquoteTC (var₀ 0)
  (toTC $ f x)
{-
  `x@(meta id args) ← newMeta =<< quoteTC A
    where _ → typeError $ strErr "Impossible case is reached" ∷ []
  x   ← unquoteTC {A = A} `x
  toTC $ f x
-}  
{-
`λ : {P : A → Set ℓ} (x : A) → P x → ○ (∀ y → P y)
`λ {A = A} {P} x t = {!!}
-}
