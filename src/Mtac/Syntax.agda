{-# OPTIONS -v mtac:45 --omega-in-omega #-}

module Mtac.Syntax where

open import Prelude
open import Reflection.Extended 

open import Mtac.Core
open import Mtac.Pattern
open import Mtac.Operation

Pbase-syntax : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {P : A → Set ℓ₂} (x : A) (px : ○ P x) → Patt P
Pbase-syntax  = Pbase

syntax Pbase-syntax x b = [ x ]⇒ b

Ptele-syntax : {P : A → Set ℓ} → (C → Patt P) → Patt P
Ptele-syntax {C = C} = Ptele C

syntax Ptele-syntax (λ x → e) = x ▻ e

mmatch-syntax = mmatch
syntax mmatch-syntax (λ x → τ) a pats = mcase a ∶ x ⇒ τ of pats

mcase_of_ : {ℓ : Level} {P : A → Set ℓ} (a : A) → Patts P (suc n) → ○ P a
mcase_of_ {P = P} a xs = mmatch P a xs

pattern _end pat = pat ∷ []
pattern _∣_ x xs = x ∷ xs

∣_ : A → A
∣_ x = x

infixl 0 mcase_of_
infix  0 mmatch-syntax
infixr 1 ∣_
infixr 2 _∣_  
infix  3 _end
infixr 5 Ptele-syntax
infixr 5 Pbase-syntax
