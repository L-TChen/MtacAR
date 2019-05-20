{-# OPTIONS -v mtac:45 --omega-in-omega #-}

module Mtac.Syntax where

open import Prelude
open import Reflection.Extended 

open import Mtac.Core
open import Mtac.Pattern
open import Mtac.Operation

Pbase-syntax : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {P : A → Set ℓ₂} (x : A) (px : ○ P x) → Patt P
Pbase-syntax  = Pbase

syntax Pbase-syntax x b = x ⇒ b

Ptele-syntax : {P : A → Set ℓ} → (C → Patt P) → Patt P
Ptele-syntax {C = C} = Ptele C

Ptele-syntax2 : {P : A → Set ℓ} (C : Set ℓ′) → (C → Patt P) → Patt P
Ptele-syntax2 C f = Ptele C f

syntax Ptele-syntax (λ x → e)    = x ▻ e
syntax Ptele-syntax2 C (λ x → e) = x ∶ C ▻ e

mmatch-syntax = mmatch
syntax mmatch-syntax (λ x → τ) a pats = mcase a ∶ x ⇒ τ of pats

mcase_of_ : {ℓ : Level} {P : A → Set ℓ} (a : A) → Patts P (suc n) → ○ P a
mcase_of_ {P = P} a xs = mmatch P a xs

pattern _end pat = pat ∷ []
pattern _∣_ x xs = x ∷ xs

∣_ : A → A
∣_ x = x

infixl 1 mcase_of_
infix  1 mmatch-syntax
infixr 2 ∣_
infixr 3 _∣_  
infix  4 _end
infixr 5 Ptele-syntax
infixr 5 Ptele-syntax2
infixr 5 Pbase-syntax
