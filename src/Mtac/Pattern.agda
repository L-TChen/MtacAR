{-# OPTIONS --omega-in-omega --without-K #-}

module Mtac.Pattern where

open import Prelude
open import Reflection.Extended

open import Mtac.Core

------------------------------------------------------------------------
-- A `Patt`ern is essentially a context with a pattern to match on the
-- left hand side and a possible term to return on the right hand
-- side. Setω is used to contain arbitrary type in any universe level.
-- universe polymorphism
data Patt (P : A → Set ℓ) : Setω where
  Pbase : (x : A)      (px : ○ (P x))     → Patt P
  Ptele : (C : Set ℓ′) (f : C → Patt P) → Patt P

data Patts (P : A → Set ℓ) : ℕ → Setω where
  []   : Patts P 0
  _∷_  : Patt P → Patts P n → Patts P (suc n)

------------------------------------------------------------------------
-- `split` takes a pattern apart into LHS and RHS (see above).
private
  variable
    P : A → Set ℓ

split : Patt P → TC (Term × Term)
split (Pbase x px) = ⦇ quoteTC x , quoteTC px ⦈
split (Ptele C f)  =
  quoteTC C >>= newMeta >>= unquoteTC >>= λ x → split (f x)

------------------------------------------------------------------------
-- `mmatch` takes a list of patterns and return the RHS of the first
-- matched pattern.
match1 : Term → Patt P → TC Term
match1 `a pat = do
  `lhs , `rhs ← split pat
  `a =′ `lhs
  return `rhs

matchMany : Term → Patts P (suc n) → TC Term
matchMany `a (x ∷ [])            = match1 `a x
matchMany `a (x ∷ patts@(_ ∷ _)) = match1 `a x <|> matchMany `a patts

mmatch : (P : ∀ A → Set ℓ) (a : A) → Patts P (suc n) → ○ (P a)
mmatch P a patts = joinTC○ do
  `a ← quoteTC a
  (unquoteTC =<< matchMany `a patts) <|> return (throw NoPatternMatched)
