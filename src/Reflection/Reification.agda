module Reflection.Reification where

open import Prelude
open import Reflection.Base

infixl 1 _>>=R_

postulate
  Exception   : Set
  showExcept  : Exception → String
  NotFound    : Exception
  EmptyClause : Exception 
--------------------------------------------------------------------------------
-- Rei: A monad for typed tactic programming in Agda
-- (a mimic of Mtac)

record Rei (A : Set ℓ) : Set where
  constructor rei
  field
    tm : TC (Exception ⊎ Term)
open Rei public

returnR : A → Rei A
returnR a = rei ⦇ inj₂ (quoteTC a) ⦈

bindR : {A B : Set ℓ} → Rei A → (A → Rei B) → Rei B
bindR {A = A} (rei ta) f = rei $
  ta >>= λ { (inj₁ err) → return (inj₁ err)
           ; (inj₂ ta)  → bindTC {A = A} (unquoteTC ta) (tm ∘ f) }
_>>=R_ = bindR

instance
  ReiMonad : Monad Rei
  ReiMonad = record
    { return = returnR
    ; _>>=_  = bindR 
    }

postulate
  identityˡ : ∀ (a : A) (f : A → Rei B) → (returnR a >>= f) ≡ f a
  --    rei ((quoteTC a >>=TC unquoteTC) >>=TC (λ x → tm (f x))) ≡ f a
  identityʳ : ∀ (ma : Rei A) → (ma >>= return) ≡ ma
  --    rei ((tm ma >>=TC unquoteTC) >>=TC (λ x → quoteTC x)) ≡ ma
  assoc : ∀ (ma : Rei A) (f : A → Rei B) (g : B → Rei C)
    → (ma >>=R f >>=R g) ≡ (ma >>=R (λ x → f x >>=R g))
  --    
  --  rei (
  --    (((tm ma >>=TC unquoteTC) >>=TC (λ x → tm (f x))) >>=TC unquoteTC)
  --    >>=TC (λ x → tm (g x)))
  --    ≡
  --  rei ((tm ma >>=TC unquoteTC) >>=TC
  --       (λ x → (tm (f x) >>=TC unquoteTC) >>=TC (λ x₁ → tm (g x₁))))

--------------------------------------------------------------------------------
--

macro
  run : Rei A → Script
  run (rei ma) hole = do
    inj₂ ta ← ma
      where (inj₁ err) → typeError [ strErr (showExcept err) ]
    unify ta hole

raise : Exception → Rei A
raise str = rei $ return (inj₁ str)

raise′ : Exception → TC (Exception ⊎ Term)
raise′ = return ∘ inj₁

_catch_ : Rei A → (Exception → Rei A) → Rei A
(rei ma) catch handler = rei $
  ma >>= λ { (inj₁ err) → tm $ handler err
           ; (inj₂ ta)  → return (inj₂ ta) }

print : String → Rei ⊤
print str = rei $ typeError [ strErr str ]

data Patt {A : Set} (P : A → Set) : Set₁ where
  Pbase : (x : A) → (px : Rei $ P x) → Patt P
  Ptele : {C : Set} → (f : ∀ (x : C) → Patt P) → Patt P

match : {A : Set} (P : A → Set) (a : A)
  → List (Patt P) → Rei (P a)
match P a []                = raise EmptyClause
match P a (Pbase b (rei tbx) ∷ xs) = rei do
  whta ← reduce =<< quoteTC a
  whtb ← reduce =<< quoteTC b
  if ⌊ whta ≟ whtb ⌋ then tbx else (tm $ match P a xs)
match P a (Ptele f ∷ xs) = {!!}

tauto : Rei (∀ x y → x + y ≡ y + x)
tauto = rei {!!}

{-# NON_TERMINATING #-}
fix : {A : Set} {P : A → Set}
  → ((∀ x → Rei $ P x) → ∀ x → Rei $ P x)
  → (x : A) → Rei $ P x
fix f x = f (fix f) x

-- Mendler-style ? 
fix′ : {A : Set} {P : A → Set} (M : Set → Set)
  → (∀ x → M (P x) → Rei (P x))
  → ((∀ x → M $ P x) → ∀ x → M $ P x)
  → ∀ x → Rei $ P x
fix′ M h f x = {!!}

-- data Goal : Set₁ where
--   MV     : {A : Set} → A → Goal
--   AHyp   : {A : Set} → (A → Goal) → Goal
--   HypRem : {A : Set} → A → Goal → Goal

-- Goals : Set₁
-- Goals = List Goal


-- record TacMonad (M : Set₁ → Set₁) : Set₂ where
--   field
--     ⦃ monad ⦄ : Monad M
--     ⦃ alt   ⦄ : Alternative M
    
-- open TacMonad ⦃...⦄ public

-- Tactic : Set₂
-- Tactic = ∀ {M} ⦃ _ : TacMonad M ⦄ → Goal → M Goals

-- bind : Tactic → Tactic → Tactic 
-- bind t u g = {!return ?!}
