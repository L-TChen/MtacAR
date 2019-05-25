{-# OPTIONS --without-K --omega-in-omega #-}

module Mtac.TyList where

open import Prelude.Core
open import Reflection.Extended
open import Mtac.Core
open import Mtac.Syntax

Dyn : ∀ {ℓ} → Set (lsuc ℓ)
Dyn {ℓ} = Σ (Set ℓ) λ A → A

Dyns : Set (lsuc ℓ)
Dyns {ℓ} = List (Dyn {ℓ})

toDyn : ℕ → Type → TC (Dyn {ℓ})
toDyn n `A = do
  A ← unquoteTC `A
  a ← unquoteTC (var₀ 0)
  return {A = Dyn} (A , a)

{-# TERMINATING #-}
lookup : (A : Set ℓ) → Dyns {ℓ} → ○ A
lookup {ℓ} A dyns = mcase dyns of 
  ∣ x ∶ _ , ds ∶ _ , ((A , x) ∷ ds) ⇒ return x
  ∣ d ∶ _ , ds ∶ _ , (d ∷ ds)       ⇒ lookup A ds
  ∣ []                              ⇒ throw NotFound
  end

context : ○ (Dyns {ℓ})
context = {!!}
