{-# OPTIONS --without-K --safe -v mtac:100 #-}

module Mtac.Binders where

open import Prelude.Core
open import Prelude.Maybe

open import Reflection.Extended
open import Reflection.Extended.DeBruijn

open import Mtac.Core


------------------------------------------------------------------------
-- Check if a particular variable n : ℕ is used in a term.

_#_ : ℕ → Term → Bool
n # t = not $ recTerm record anyTermRec
  { Pvar = λ i args n → i == n || any ((_$ n) ∘ unArg ) args
  ; Plam = λ _ t n    → unAbs t (suc n)
  ; Ppi = λ ar t n    → unArg ar n || unAbs t (suc n)
  } t n

_##_ : ℕ → Cxt → Bool
n ## []      = true
n ## (x ∷ Γ) = n # (unArg x) && (n ∸ 1) ## Γ

------------------------------------------------------------------------
-- reset xₙ to xₘ 
-- 
reset : ℕ → ℕ → Term → Term
reset n m t = recTerm record idRec
  { Pvar = λ { i args (n , m) → let arg' = ((λ { (arg i x) → arg i (x (n , m)) }) <$> args) in
    if i == n
      then var m arg'
      else var i arg' }
  ; Plam = λ { v (abs s t) (n , m) → lam v (abs s (t (1 + n , 1 + m))) } 
  ; Ppi  = λ { (arg i dom) (abs s cod) (n , m) →
    pi (arg i (dom (n , m))) (abs s (cod (1 + n , 1 + m))) }
  } t (n , m)

-- Pick a variable to abstract where freshness should be checked in advance 
absVar : ℕ → Term → Term
absVar n t = vLam "_" $ reset (suc n) 0 (weaken 1 t) 


mabs : {P : A → Set ℓ} (x : A) → P x → ○ ((y : A) → P y)
mabs x px = throw NotImplemented

{-do
  t@(var₀ i) ← liftTC $ reduce =<< quoteTC x
    where t → throw (NotVariable t)
    
  cxt    ← liftTC getContext
  (guard $ (i ∸ 1) ## take i cxt) <|> throw (VariableNotFresh t)
  
  liftTC $ unquoteTC =<< (absVar i <$> quoteTC px)
-}
------------------------------------------------------------------------
-- name restriction / local name : ν x . t

nu : (A → ○ B) → ○ B
nu {A = A} f = throw NotImplemented

{-joinTC○ do
  `A ← quoteTC A
  λ′ (vArg `A) do
    a ← unquoteTC (var₀ 0)
    term `fa ← toTC (f a)  where _ → return (f a)
    return $ if 0 # `fa
      then ◎ returnTC (term `fa)
      else throw StuckTerm
-}
