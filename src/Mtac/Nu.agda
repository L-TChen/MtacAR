{-# OPTIONS --safe --without-K #-}

module Mtac.Nu where

open import Prelude.Core
open import Reflection.Extended

open import Mtac.Core

------------------------------------------------------------------------
-- name restriction operator ν x . t
--

_hasMeta_ : Term → Meta → Bool
t hasMeta x = recTerm {⊤ → Bool} 
  record anyTermRec { Pmeta = λ y bs _ → x == y || any ((_$ tt) ∘ unArg) bs } t _ 

nu : (A : Set ℓ) → (A → ○ B) → ○ B
nu {ℓ} A f = ◎ runSpeculative do
  `A ← quoteTC A
  `a@(meta x args) ← newMeta `A
    where _ → return (error (NoMeta `A) , false)
    
  term `fa ← toTC ∘ f =<< unquoteTC `a
    where tac → return (tac , false)
    
  `fa ← reduce `fa
  return $ if `fa hasMeta x then (error $ StuckTerm `fa) , false else (term `fa , false)
