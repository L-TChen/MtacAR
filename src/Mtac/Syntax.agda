{-# OPTIONS -v mtac:50 --type-in-type #-}

module Mtac.Syntax where

open import Prelude
open import Reflection.Extended 

open import Mtac.Core
open import Mtac.Pattern
open import Mtac.Operation

infixl 0 mcase_of_
infix  0 mmatch-syntax
infixr 4 Ptele-syntax
infixr 4 Pbase-syntax
infixr 1 _∣_
infixr 2 ∣_
infix  2 _end

Pbase-syntax : {P : A → Set} (x : A) (px : ○ P x) → Patt P
Pbase-syntax  = Pbase
syntax Pbase-syntax x b = x ⇒ b

Ptele-syntax : {P : A → Set} → (C → Patt P) → Patt P
Ptele-syntax {C = C} {P} = Ptele C  

syntax Ptele-syntax (λ x → e) = x :> e

mmatch-syntax = mmatch
syntax mmatch-syntax (λ x → τ) a pats = mcase a ∶ x ⇒ τ of pats

mcase_of_ : {P : A → Set} (a : A) → Patts P n → ○ P a
mcase_of_ {P = P} a xs = mmatch P a xs

∣_ : A → A
∣_ x = x

_∣_ : A → Vec A n → Vec A (1 + n)
x ∣ xs = x ∷ xs

_end : A → Vec A 1
x end = x ∷ []

------------------------------------------------------------------------
-- Benchmark Example 1:
{-# TERMINATING #-}
tauto : (P : Set) → ○ P
tauto P = do
  mprint "\n--------------STARTING----------------"
  mcase P of
    ∣ ⊤                 ⇒ return tt
    ∣ p :> q :> (p × q) ⇒ ⦇ tauto p , tauto q ⦈
    ∣ p :> q :> (p ⊎ q) ⇒
      try     (tauto p >>= return ∘ inj₁)
      finally (tauto q >>= return ∘ inj₂)
    ∣ p :> p            ⇒ throw NotFound
    end

_ : ⊥ ⊎ ⊥ ⊎ ⊤ × ⊤
_ = {! run (tauto $ ⊥ ⊎ ⊥ ⊎ ⊤ × ⊤) !}
