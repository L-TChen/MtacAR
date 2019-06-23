{-# OPTIONS --without-K --safe #-}

module Mtac.Binders where

open import Prelude
open import Reflection.Extended

open import Mtac.Core

-- Check if a particular variable n : ℕ is used in a term.
_#_ : ℕ → Term → Bool
n # t = not $ recTerm record anyTermRec
  { Pvar = λ i args n → i == n || any ((_$ n) ∘ unArg) args
  ; Plam = λ _ t  n   → unAbs t (suc n)
  ; Ppi  = λ ar t n   → unArg ar n || unAbs t (suc n)
  } t n

_##_ : ℕ → Cxt → Bool
zero  ## Γ       = true
suc n ## []      = true
suc n ## (x ∷ Γ) = n # (unArg x) && n ## Γ

rename : ℕ → ℕ → Term → Term
rename n m t = recTerm {A = ℕ × ℕ → Term} record idRec
  { Pvar = λ { i args nm@(n , m) → if i == n
      then var m (map (_$ nm) <$> args)
      else var i (map (_$ nm) <$> args) }
  ; Plam = λ v t nm → lam v ((bimap suc suc nm |>_) <$> t)
  ; Ppi  = λ dom cod nm →
    pi ((nm |>_) <$> dom) $ (bimap suc suc nm |>_) <$> cod
  } t (n , m)

absVar : String → ℕ → Term → Term
absVar s n t = vLam s $ rename (1 + n) 0 (weaken 1 t)

mabs : {P : A → Set ℓ} (x : A) → (name : String) → P x → ○ ((y : A) → P y)
mabs x s px = ◎ do
  var₀ i ← quoteTC! x
    where t → throw′ (NotVariable t)

  ifM ⦇ (i ##_) getContext ⦈
    then ⦇ (term ∘ absVar s i) (quoteTC px) ⦈
    else throw′ (VariableNotFresh $ var₀ i)

-- name restriction / local name : ν x . t
nu : (A → ○ B) → ○ B
nu {A = A} f = ◎ do
  `A ← quoteTC A
  extendContext (vArg `A) do
    a ← unquoteTC (var₀ 0)

    term `fa ← toTC (f a)
      where tac → return tac

    case strengthen 1 `fa of λ where
      nothing  → return $ error (LocalName `fa)
      (just t) → return $ term t
