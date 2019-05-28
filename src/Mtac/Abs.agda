{-# OPTIONS --without-K --safe #-}

module Mtac.Abs where

open import Prelude.Core
open import Prelude.Maybe

open import Reflection.Extended
open import Reflection.Extended.DeBruijn

open import Mtac.Core

------------------------------------------------------------------------
-- Check if a particular variable n : ℕ is in a term.

_#_ : ℕ → Term → Bool
n # t = not $ recTerm record anyTermRec
  { Pvar = λ i args n → i == n || any ((_$ n) ∘ unArg ) args
  ; Plam = λ _ t n    → unAbs t (suc n)
  ; Ppi = λ ar t n    → unArg ar n || unAbs t (suc n)} t n

-- check if a variable is used in a context which is in reverse order

_##_ : ℕ → Cxt → Bool
n ## []      = true
n ## (x ∷ Γ) = n # (unArg x) && (n ∸ 1) ## Γ

------------------------------------------------------------------------
-- reset var n args to var m args 
-- 
reset : ℕ → ℕ → Term → Term
reset n m t = recTerm {A = ℕ × ℕ → Term} record idRec
  { Pvar = λ { i args (n , m) → let arg' = ((λ { (arg i x) → arg i (x (n , m)) }) <$> args) in
    if i == n
      then var m arg'
      else var i arg' }
  ; Plam = λ { v (abs s t) (n , m) → lam v (abs s $ t (n + 1 , m + 1)) } 
  ; Ppi  = λ { (arg i dom) (abs s cod) (n , m) → pi (arg i $ dom (n , m)) (abs s (cod (n + 1 , m + 1))) }
  } t (n , m)

-- Pick a variable to abstract whose freshness should be checked in advance 
pickVar : ℕ → Term → Term
pickVar n t = vLam "_" $ reset (suc n) 0 (weaken 1 t) 

-- if x is a variable in the context `var₀ i`, for 0 ≤ i < n = length
-- Γ, and `var₀ j` does not depend on `var₀ i`, then for px : P x we
-- can return λ y → px[y/x] (weaken every (var₀ j) in px by 1) and
-- replace x by (var 0)

mabs : {P : A → Set ℓ} (x : A) → P x → ○ ((y : A) → P y)
mabs {A = A} {P} x px = do
  t@(var₀ i) ← liftTC $ quoteTC x >>= reduce
    where t → throw (NotVariable t)
  cxt    ← liftTC getContext
  (guard $ (i ∸ 1) ## take i cxt) <|> throw (VariableNotFresh t)
  liftTC $ unquoteTC =<< pickVar i <$> quoteTC px
