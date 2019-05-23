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

------------------------------------------------------------------------
-- name restriction operator ν x . t
--

_hasMeta_ : Term → Meta → Bool
t hasMeta x = recTerm
  record anyTermRec { Pmeta = λ y xs → x == y || any unArg xs  } t

nu : (A : Set ℓ) → (A → ○ B) → ○ B
nu {ℓ} A f = ◎ runSpeculative do
  `a@(meta x args) ← newMeta =<< quoteTC A
    where _ → typeError $ strErr "No meta variable is created." ∷ []
  term `fa ← toTC ∘ f =<< unquoteTC {ℓ} {A = A} `a
    where tac → return (tac , false)
  `fa ← reduce `fa
  return $ if `fa hasMeta x then (error $ StuckTerm `fa) , false else (term `fa , false)


------------------------------------------------------------------------
-- lambda abstraction λ x . t
-- to check if a varialbe x_i in the context x_n-1 ... x_i ... x_ 0 is free in t ,
-- we first do lambda abstractions t' = λ x_{i-1} ... x_0 . t
-- then compare t' with (λ x_i. t') x after whnf reduction for a new metavariable x.
-- Note that λ x . t is in whnf, so nothing but the substitution x for x_i is performed.

{-
_isFreshFor_ : ℕ → A → TC Bool
n isFreshFor t = {!!}

mabs : {P : A → Set ℓ} (x : A) → P x → ○ (∀ y → P y)
mabs {A = A} {P} x t = {!!}

-}
