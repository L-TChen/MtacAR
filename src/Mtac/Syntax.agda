{-# OPTIONS --without-K --omega-in-omega #-}

------------------------------------------------------------------------
-- Syntax configuration: everything is subject to change.

module Mtac.Syntax where

open import Prelude hiding (_∷_; [])
open import Reflection.Extended

open import Mtac.Core
open import Mtac.Pattern
open import Mtac.Binders

Pbase-syntax : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {P : A → Set ℓ₂} (x : A) (px : ○ P x) → Patt P
Pbase-syntax  = Pbase

syntax Pbase-syntax x b = x ⇒ b

Ptele-syntax2 : {P : A → Set ℓ} (C : Set ℓ′) → (C → Patt P) → Patt P
Ptele-syntax2 C f = Ptele C f

syntax Ptele-syntax2 C (λ x → e) = x ∶ C , e

mmatch-syntax = mmatch
syntax mmatch-syntax f a pats = mcase a ∶ f of pats

mcase_of_ : {P : A → Set ℓ} (a : A) → Patts P (suc n) → ○ P a
mcase_of_ {P = P} a xs = mmatch P a xs



pattern _end pat = pat ∷ []
pattern _∣_ x xs = x ∷ xs

∣_ : {A : Setω} → A → A
∣_ x = x

nu-syntax : (A : Set ℓ) → (A → ○ B) → ○ B
nu-syntax A = nu {A = A}

syntax nu-syntax A (λ x → e) = ν x ∶ A ⇒ e

abs-syntax : {P : A → Set ℓ} (x : A) → ○ P x → ○ (∀ y → P y)
abs-syntax x ○px = mabs x "" =<< ○px

syntax abs-syntax x ○px = ƛ x ⇒ ○px

macro
  Proof_∎ = runTT

infix -100 Proof_∎
infixl -10 mcase_of_ mmatch-syntax
infixr -8 nu-syntax abs-syntax
infixr -8 ∣_
infixr -7 _∣_
infix  -6 _end
infixr -5 Ptele-syntax2 Pbase-syntax
