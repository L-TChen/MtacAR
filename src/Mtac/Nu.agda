{-# OPTIONS --safe --without-K #-}

module Mtac.Nu where

open import Prelude.Core
open import Reflection.Extended

open import Mtac.Core

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
