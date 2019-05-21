--{-# OPTIONS --without-K #-}
module Mtac.Core.MonadLaw where

open import Prelude.Core

open import Reflection.Extended
open import Relation.Binary.PropositionalEquality hiding ([_])

open import Mtac.Core
--------------------------------------------------------------------------------
-- Function extensionality
private
  postulate
    funext : ∀ {f g : A → B} → ((a : A) → f a ≡ g a) → f ≡ g
  
--------------------------------------------------------------------------------
-- TC is a monad

postulate
  identityTCˡ : {A : Set ℓ} {B : Set ℓ′} {a : A} {f : A → TC B}
    → bindTC (returnTC a) f ≡ f a
  identityTCʳ : {A : Set ℓ} {ma : TC A}
    → bindTC ma returnTC ≡ ma
  assocTC     : {A : Set ℓ₁} {B : Set ℓ₂} {C : Set ℓ₃} (ma : TC A) (f : A → TC B) (g : B → TC C)
    → (ma >>= f >>= g) ≡ (ma >>= (λ x → f x >>= g))
      
○-pre : Set ℓ → Set
○-pre A = TC Term
  
abstract
  assoc :(ma : ○-pre A) (f : A → ○-pre B) (g : B → TC Term)
      → bindTC (bindTC (bindTC (bindTC ma unquoteTC) f) unquoteTC) g
        ≡ bindTC (bindTC ma (unquoteTC {A = A})) (λ x → bindTC (bindTC (f x) (unquoteTC {A = B})) g)
  assoc ma f g = begin
    bindTC (bindTC (bindTC (bindTC ma unquoteTC) f) unquoteTC) g
      ≡⟨ assocTC (bindTC (bindTC ma unquoteTC) f) unquoteTC g ⟩
    bindTC (bindTC (bindTC ma unquoteTC) f) (λ x → bindTC (unquoteTC x) g)
      ≡⟨ assocTC (bindTC ma unquoteTC) f (λ x → bindTC (unquoteTC x) g) ⟩
    bindTC (bindTC ma unquoteTC) (λ a → bindTC (f a) (λ t → bindTC (unquoteTC t) g))
      ≡⟨ cong (bindTC (bindTC ma unquoteTC)) (funext λ t → sym (assocTC (f t) unquoteTC g)) ⟩ 
    bindTC (bindTC ma unquoteTC) (λ a → bindTC (bindTC (f a) unquoteTC) g) ∎
    where open ≡-Reasoning
    
postulate
  -- 1. `quoteTC` is injective. If `a` and `b` are internally equal, then they are the definitionally equal.
  quoteTC-injective  : (a b : A) → quoteTC a ≡ quoteTC b → a ≡ b
  -- 2. `quote-unquote`: `quoteTC a` followed by `unquoteTC {A = A}` is actually `return a`.
  quote-unquote : (a : A) → bindTC (quoteTC a) (unquoteTC {A = A}) ≡ returnTC a
  
identityˡ : (a : A) (f : A → TC B)  → bindTC (bindTC (quoteTC a) unquoteTC) f ≡ f a
identityˡ a f = begin
  bindTC (bindTC (quoteTC a) unquoteTC) f  ≡⟨ cong (λ ma → bindTC ma f) (quote-unquote a) ⟩
  bindTC (returnTC a) f                   ≡⟨ identityTCˡ ⟩ 
  f a ∎
  where open ≡-Reasoning
  
postulate
  -- 3. Impose `(○-pre A / ○-eq) ≃ ○ A`: Identify `mta` and `mtb` if
  -- they are observationally equal by `unquote`

  ○-preeq : ∀ {A : Set ℓ} (mta mtb : ○-pre A)
    → bindTC mta (unquoteTC {A = A}) ≡ bindTC mtb (unquoteTC {A = A}) → mta ≡ mtb
  
abstract
  returnTC-injective : (a b : A) → returnTC a ≡ returnTC b → a ≡ b
  returnTC-injective {A = A} a b eq = quoteTC-injective _ _ (○-preeq {A = A} (quoteTC a) (quoteTC b) (begin
    bindTC (quoteTC a) unquoteTC
      ≡⟨ quote-unquote a ⟩
    returnTC a
      ≡⟨ eq ⟩
    returnTC b
      ≡⟨ sym (quote-unquote b) ⟩  
    bindTC (quoteTC b) unquoteTC ∎))
    where open ≡-Reasoning
    
  identityʳ : (A : Set ℓ) (mta : ○-pre A) → bindTC (bindTC mta (unquoteTC {A = A})) quoteTC ≡ mta
  identityʳ A mta = ○-preeq {A = A} (bindTC (bindTC mta (unquoteTC {A = A})) quoteTC) mta (begin
    bindTC (bindTC (bindTC mta (unquoteTC {A = A})) quoteTC) unquoteTC
      ≡⟨ cong (λ ma → bindTC ma (unquoteTC {A = A})) (assocTC mta (unquoteTC {A = A}) quoteTC) ⟩
    bindTC (bindTC mta (λ t → bindTC (unquoteTC {A = A} t) quoteTC)) unquoteTC
      ≡⟨ assocTC mta (λ t → bindTC (unquoteTC {A = A} t) quoteTC) unquoteTC ⟩
    bindTC mta (λ t → bindTC (bindTC (unquoteTC {A = A} t) quoteTC) unquoteTC)
      ≡⟨ cong (bindTC mta) (funext λ t → assocTC (unquoteTC {A = A} t) quoteTC unquoteTC) ⟩
    bindTC mta (λ t → unquoteTC {A = A} t >>= (λ a → quoteTC a >>= unquoteTC))
      ≡⟨ cong (bindTC mta) (funext λ t → cong (bindTC (unquoteTC {A = A} t)) (funext (λ a → quote-unquote a))) ⟩
    bindTC mta (λ t → unquoteTC t >>= (λ a → returnTC a))
      ≡⟨ cong (bindTC mta) (funext λ t → identityTCʳ ) ⟩ 
    bindTC mta unquoteTC ∎)
    where open ≡-Reasoning
  
  ○-identityˡ : {A : Set ℓ₁} {B : Set ℓ₂} (a : A) (f : A → ○ B)
    → (◎ bindTC (bindTC (quoteTC a) (λ `a → returnTC (term `a))) (unquoteBind f)) ≡ f a
  ○-identityˡ {ℓ₁} {ℓ₂} {A} {B } a f = begin
    bind○ (return○ a) f
      ≡⟨⟩
    (◎ bindTC (bindTC (quoteTC a) (return ∘ term)) (unquoteBind f))
      ≡⟨ cong ◎_ (assocTC (quoteTC a) (return ∘ term) (unquoteBind f)) ⟩
    (◎ bindTC (quoteTC a) (λ x → bindTC (return (term x)) (unquoteBind f)))
      ≡⟨ cong ◎_ (cong (bindTC (quoteTC a)) (funext λ t → identityTCˡ)) ⟩
    (◎ bindTC (quoteTC a) λ x → (unquoteBind f) $ term x)
      ≡⟨⟩
    (◎ bindTC (quoteTC a) λ x → bindTC (unquoteTC x) (toTC ∘ f))
      ≡⟨ cong ◎_ (sym (assocTC (quoteTC a) unquoteTC _)) ⟩
    (◎ bindTC (bindTC (quoteTC a) unquoteTC) (toTC ∘ f))
      ≡⟨ cong ◎_ (identityˡ a (toTC ∘ f)) ⟩ 
    (◎ toTC (f a))
      ≡⟨⟩ 
    f a ∎
    where open ≡-Reasoning

  ○-fail : ∀ {A : Set ℓ} {B : Set ℓ′} (f : A → ○ B) (msg : String) → (fail msg >>= f) ≡ fail msg
  ○-fail f msg = cong ◎_ (begin
    bindTC (returnTC (blocked msg)) (unquoteBind f)
      ≡⟨ identityTCˡ ⟩
    (unquoteBind f) (blocked msg)
      ≡⟨⟩ 
    returnTC (blocked msg) ∎)
    where open ≡-Reasoning
    
postulate
  ○-identityʳ : (ma : ○ A) → (bind○ ma return○) ≡ ma
  ○-assoc : (ma : ○ A) (f : A → ○ B) (g : B → ○ C)
    → bind○ (bind○ ma f) g ≡ bind○ ma (λ x → bind○ (f x) g)
      
 {- 
  ○-identityʳ : {A : Set ℓ} (ma : ○ A) → (ma >>= return) ≡ ma
  ○-identityʳ {A = A} (◎ mta) = cong ◎_ {!!}
    where open ≡-Reasoning
  
  ○-assoc : {A : Set ℓ₁} {B : Set ℓ₂} {C : Set ℓ₃} (ma : ○ A) (f : A → ○ B) (g : B → ○ C)
      → (ma >>= f >>= g) ≡ (ma >>= (λ x → f x >>= g))
  ○-assoc ma f g = {!!}
  -}

