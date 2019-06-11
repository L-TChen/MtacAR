{-# OPTIONS --without-K --omega-in-omega #-}

module Mtac.HListω where

open import Prelude
open import Reflection.Extended

open import Mtac hiding (lookup)

Dyn : (ℓ : Level) → Set (lsuc ℓ)
Dyn ℓ = Σ (Set ℓ) id

toDyn : {A : Set ℓ} → Type × Term → TC (Dyn ℓ)
toDyn {ℓ} {A} (`A , `a) = do
  A ← unquoteTC {A = Set ℓ} `A
  bindTC (unquoteTC {A = A} `a) λ a → -- why instance arguments cannot solve this?
    return (A , a)

-- heterogeneous list
data HListω : Setω where
  []  : HListω
  _∷_ : Dyn ℓ → HListω → HListω

lookup : (A : Set ℓ) → HListω → ○ A
lookup A []             = ⦇⦈
lookup A ((x , B) ∷ xs) =
  ifM (A ≟ B) then coe ⦇ x ⦈ else lookup A xs
