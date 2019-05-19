{-# OPTIONS -v mtact:50 --type-in-type #-}

module Mtac.Syntax where

open import Prelude
open import Mtac.Core
open import Mtac.Construct
open import Mtac.Operation

infix  0 mfix-syntax 
infixl 0 mcase_of_
infix  0 mmatch-syntax
infixr 4 Ptele-syntax
infixr 4 Pbase-syntax
infixr 1 _∣_
infixr 2 ∣_
infix  2 _end

mfix-syntax   = mfix
syntax mfix-syntax A (λ x → e) (λ f → t) = mfix f ∶⟨ x ∶ A ⟩⇒ e ≔ t

Pbase-syntax : {P : A → Set} (x : A) (px : ○ P x) → Patt A P
Pbase-syntax  = Pbase
syntax Pbase-syntax x b = x ⇒ b

Ptele-syntax : {P : A → Set} → (C → Patt A P) → Patt A P
Ptele-syntax  = Ptele

syntax Ptele-syntax (λ x → e) = x :> e

mmatch-syntax = mmatch
syntax mmatch-syntax (λ x → τ) a pats = mcase a ∶ x ⇒ τ of pats

mcase_of_ : {P : A → Set} (a : A) → Patts A P n → ○ P a
mcase_of_ {P = P} a xs = mmatch P a xs

∣_ : A → A
∣_ x = x

_∣_ : A → Vec A n → Vec A (1 + n)
x ∣ xs = x ∷ xs

_end : A → Vec A 1
x end = x ∷ []

------------------------------------------------------------------------
-- Benchmark Example 1:

tauto : (P : Set) → ○ P
tauto P = do
  mprint "\n---------------------STARTING-------------------"
  (mfix f ∶⟨ x ∶ Set ⟩⇒ x ≔ λ x →
   mcase x of
    ∣ ⊤ ⇒ return tt
    ∣ p₁ :> p₂ :> (p₁ × p₂) ⇒ ⦇ f p₁ , f p₂ ⦈
    ∣ p₁ :> p₂ :> (p₁ ⊎ p₂) ⇒
      try     (f p₁ >>= return ∘ inj₁)
      finally (f p₂ >>= return ∘ inj₂)
    ∣ p :> p ⇒ throw NotFound
    end) P

{-# TERMINATING #-}
tauto2 : (P : Set) → ○ P
tauto2 P = do
  mprint "\n---------------------STARTING-------------------"
  mcase P of
    ∣ ⊤                 ⇒ return tt
    ∣ p :> q :> (p × q) ⇒ ⦇ tauto2 p , tauto2 q ⦈
    ∣ p :> p            ⇒ throw NotFound
    end

sample : Term
sample = quoteTerm (Ptele {P = λ (x : Set) → x} (λ p →
   Ptele
   (λ q →
      Pbase (p × q)
      ((monad⇒applicative IApplicative.<*>
        (monad⇒applicative IApplicative.<*>
         IApplicative.pure monad⇒applicative _,_)
        (tauto2 p))
       (tauto2 q)))))
