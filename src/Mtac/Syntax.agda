{-# OPTIONS -v mtac:45 --without-K --omega-in-omega #-}

------------------------------------------------------------------------
-- Syntax configuration: everything is subject to change.

module Mtac.Syntax where

open import Prelude.Core
open import Reflection.Extended

open import Mtac.Core
open import Mtac.Pattern
open import Mtac.Nu
open import Mtac.Abs



Pbase-syntax : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {P : A → Set ℓ₂} (x : A) (px : ○ P x) → Patt P
Pbase-syntax  = Pbase

syntax Pbase-syntax x b = x ⇒ b

Ptele-syntax2 : {P : A → Set ℓ} (C : Set ℓ′) → (C → Patt P) → Patt P
Ptele-syntax2 C f = Ptele C f

syntax Ptele-syntax2 C (λ x → e) = x ∶ C , e

mmatch-syntax = mmatch
syntax mmatch-syntax (λ x → τ) a pats = case a ∶ x ⇒ τ of pats

mcase_of_ : {P : A → Set ℓ} (a : A) → Patts P (suc n) → ○ P a
mcase_of_ {P = P} a xs = mmatch P a xs

pattern _end pat = pat ∷ []
pattern _∣_ x xs = x ∷ xs

∣_ : {A : Setω} → A → A
∣_ x = x

nu-syntax : (A : Set ℓ) → (A → ○ B) → ○ B
nu-syntax {ℓ} = nu {ℓ}

syntax nu-syntax A (λ x → e) = ν x ∶ A ⇒ e -- ?

abs-syntax : {P : A → Set ℓ} (x : A) → P x → ○ ((y : A) → P y)
abs-syntax {ℓ} = mabs {ℓ}

syntax abs-syntax {A = A} x e = ƛ x ∶ A ⇒ e

macro
  Proof_∎ = runTT

infix -100 Proof_∎
infixl -9 mcase_of_
infix  -9 mmatch-syntax
infixr -8 nu-syntax
infixr -8 abs-syntax
infixr -8 ∣_
infixr -7 _∣_
infix  -6 _end
infixr -5 Ptele-syntax2
infixr -5 Pbase-syntax
