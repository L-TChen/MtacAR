{-# OPTIONS --without-K --safe -v mtac:100 #-}

module Mtac.Binders where

open import Prelude
open import Reflection.Extended

open import Mtac.Core

-- Check if a particular variable n : ℕ is used in a term.
_#_ : ℕ → Term → Bool
n # t = not $ recTerm record anyTermRec
  { Pvar = λ i args n → i == n || any ((_$ n) ∘ unArg ) args
  ; Plam = λ _ t n    → unAbs t (suc n)
  ; Ppi  = λ ar t n   → unArg ar n || unAbs t (suc n)
  } t n

_##_ : ℕ → Cxt → Bool
zero  ## Γ       = true
suc n ## []      = true
suc n ## (x ∷ Γ) = n # (unArg x) && n ## Γ

-- reset xₙ to xₘ 
reset : ℕ → ℕ → Term → Term
reset n m t = recTerm {A = ℕ × ℕ → Term} record idRec 
  { Pvar = λ i args nm → if i == n
      then var m (map (_$ nm) <$> args)
      else var i (map (_$ nm) <$> args)
  ; Plam = λ v t nm → lam v ((bimap suc suc nm |>_) <$> t)
  ; Ppi  = λ dom cod nm → pi ((nm |>_) <$> dom) ((bimap suc suc nm |>_) <$> cod) 
  } t (n , m)

absVar : ℕ → Term → Term
absVar n t = vLam "_" $ reset (suc n) 0 (weaken 1 t) 

mabs : {P : A → Set ℓ} (x : A) → P x → ○ ((y : A) → P y)
mabs x px = ◎ do
  `x@(var₀ i) ← quoteTC! x
    where t → throw′ (NotVariable t)
    
  ⦇ if ⦇ (i ##_) getContext ⦈
    then ⦇ (absVar i) (quoteTC px) ⦈ >>= return ∘ term
    else throw′ (VariableNotFresh `x) ⦈ 

-- name restriction / local name : ν x . t
nu : (A → ○ B) → ○ B
nu {A = A} f = joinTC○ do
  `A ← vArg <$> quoteTC A
  extendContext `A do
    a ← unquoteTC (var₀ 0)
    term `fa ← toTC (f a)
      where _ → return (f a)
    return $ if 0 # `fa
      then ◎ returnTC (term `fa)
      else throw LocalName
