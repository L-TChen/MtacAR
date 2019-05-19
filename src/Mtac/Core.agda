module Mtac.Core where

open import Prelude hiding (_⟨_⟩_)
open import Relation.Binary.PropositionalEquality hiding ([_])

open import Reflection.Extended
  
-- to be addressed properly 
Exception        = String
showExcept       = id
NotCanonical     = λ (id : Name) → show id ++ " is not canonical"
NotFound         = "Not Found"
InvalidPattern   = "Invalid Pattern"
EmptyClause      = "Empty Clause"
NoPatternMatched = "No Pattern Matched"
NotImplemented   = "Not Implemented"

-----------------------------------------------
-- A monad for typed tactic programming in Agda
record ○_ (A : Set ℓ) : Set ℓ where
  constructor ◎_
  field
    toTC : TC (Exception ⊎ Term)
open ○_ public
infix 0 ◎_
infix 0 ○_

returnR : A → ○ A
returnR a = ◎ quoteTC a TC.>>= λ t → TC.return (inj₂ t)

quoteBind : (f : A → ○ B) → Exception ⊎ Term → TC (Exception ⊎ Term)
quoteBind f (inj₁ err) = TC.return (inj₁ err)
quoteBind f (inj₂ qa)  = unquoteTC qa TC.>>= toTC ∘ f

bindR : ○ A → (A → ○ B) → ○ B
bindR (◎ ta) f = ◎ ta TC.>>= quoteBind f

joinR : TC (○ A) → ○ A
joinR ma = ◎ (ma TC.>>= (TC.return ∘ toTC) TC.>>= id)

fromTC : {A : Set} → TC A → ○ A
fromTC ma = ◎ (ma TC.>>= λ a → quoteTC a TC.>>= TC.return ∘ inj₂)

instance
  ○-Monad : Monad ○_
  ○-Monad = record
    { return = returnR
    ; _>>=_  = bindR }
  ○-MonadErr : MonadError Exception ○_
  ○-MonadErr = record
    { throw      = ◎_ ∘ throw
    ; try_catch_ = λ { (◎ a) handler → ◎ try a catch (toTC ∘ handler) }
    }
  ○-Applicative : Applicative ○_
  ○-Applicative = monad⇒applicative
  
  ○-Alternative : Alternative ○_
  ○-Alternative = record { azero = ◎ typeError [] ; _<|>_ = λ { (◎ a) (◎ b) → ◎ a <|> b } }
------------------------------------------------------------------------
-- Run a typed program

runR : ○ A → Tactic
runR (◎ ma) hole = do
  inj₂ ta ← ma   where (inj₁ err) → typeError [ strErr (showExcept err) ]
  unify ta hole
macro
  run  = runR

print : ℕ → ErrorParts → TC ⊤
print n errs = debugPrint "mtac" n errs

-- Proofs 

private
  --------------------------------------------------------------------------------
  -- Function extensionality
  postulate
    funext : ∀ {f g : A → B} → ((a : A) → f a ≡ g a) → f ≡ g
  
  --------------------------------------------------------------------------------
  -- TC is a monad
  
  postulate
    identityTCˡ : {A : Set ℓ} {B : Set ℓ′} {a : A} {f : A → TC B}
      → bindTC (TC.return a) f ≡ f a
    identityTCʳ : {A : Set ℓ} {ma : TC A}
      → bindTC ma TC.return ≡ ma
    assocTC     : {A : Set ℓ₁} {B : Set ℓ₂} {C : Set ℓ₃} (ma : TC A) (f : A → TC B) (g : B → TC C)
      → (ma TC.>>= f TC.>>= g) ≡ (ma TC.>>= (λ x → f x TC.>>= g))
      
  ○-pre : Set ℓ → Set
  ○-pre A = TC Term
  
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
    quote-unquote : (a : A) → bindTC (quoteTC a) (unquoteTC {A = A}) ≡ TC.return a
  
  identityˡ : (a : A) (f : A → TC B)  → bindTC (bindTC (quoteTC a) unquoteTC) f ≡ f a
  identityˡ a f = begin
    bindTC (bindTC (quoteTC a) unquoteTC) f  ≡⟨ cong (λ ma → bindTC ma f) (quote-unquote a) ⟩
    bindTC (TC.return a) f                   ≡⟨ identityTCˡ ⟩ 
    f a ∎
    where open ≡-Reasoning
  
  postulate
    -- 3. Impose `(○-pre A / ○-eq) ≃ ○ A`: Identify `mta` and `mtb` if they are observationally equal by `unquote`
    ○-preeq : ∀ {A : Set ℓ} (mta mtb : ○-pre A)
      → bindTC mta (unquoteTC {A = A}) ≡ bindTC mtb (unquoteTC {A = A}) → mta ≡ mtb
  
  returnTC-injective : (a b : A) → TC.return a ≡ TC.return b → a ≡ b
  returnTC-injective {A = A} a b eq = quoteTC-injective _ _ (○-preeq {A = A} (quoteTC a) (quoteTC b) (begin
    bindTC (quoteTC a) unquoteTC
      ≡⟨ quote-unquote a ⟩
    TC.return a
      ≡⟨ eq ⟩
    TC.return b
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
    bindTC mta (λ t → unquoteTC {A = A} t TC.>>= (λ a → quoteTC a TC.>>= unquoteTC))
      ≡⟨ cong (bindTC mta) (funext λ t → cong (bindTC (unquoteTC {A = A} t)) (funext (λ a → quote-unquote a))) ⟩
    bindTC mta (λ t → unquoteTC t TC.>>= (λ a → TC.return a))
      ≡⟨ cong (bindTC mta) (funext λ t → identityTCʳ ) ⟩ 
    bindTC mta unquoteTC ∎)
    where open ≡-Reasoning
  
  postulate
    ○-identityˡ : {A : Set ℓ} {B : Set ℓ′} (a : A) (f : A → ○ B)
      → (◎ bindTC (quoteTC a) (λ t → TC.return (inj₂ t)) TC.>>= quoteBind f) ≡ f a
    ○-identityʳ : {A : Set ℓ} (ma : ○ A) → (ma >>= return) ≡ ma
    ○-assoc : {A : Set ℓ₁} {B : Set ℓ₂} {C : Set ℓ₃} (ma : ○ A) (f : A → ○ B) (g : B → ○ C)
      → (ma >>= f >>= g) ≡ (ma >>= (λ x → f x >>= g))
      
  {- True for any monad 
  ○-identityˡ : {A : Set ℓ} {B : Set ℓ′} (a : A) (f : A → ○ B) → (bindR (returnR a) f) ≡ f a
  ○-identityˡ {A = A} {B = B} a f = begin
    bindR (returnR a) f
      ≡⟨⟩
    (◎ bindTC (bindTC (quoteTC a) (TC.return ∘ inj₂)) (quoteBind f))
      ≡⟨ cong ◎_ (assocTC (quoteTC a) (TC.return ∘ inj₂) (quoteBind f)) ⟩
    (◎ bindTC (quoteTC a) (λ x → bindTC (TC.return (inj₂ x)) (quoteBind f)))
      ≡⟨ cong ◎_ (cong (bindTC (quoteTC a)) (funext λ t → refl)) ⟩
    (◎ bindTC (quoteTC a) λ x → bindTC (unquoteTC x) λ y → toTC (f y))
      ≡⟨ cong ◎_ (sym (assocTC (quoteTC a) unquoteTC (toTC ∘ f))) ⟩
    (◎ bindTC (bindTC (quoteTC a) unquoteTC) (toTC ∘ f))
      ≡⟨ cong ◎_ (identityˡ a (toTC ∘ f)) ⟩ 
    (◎ toTC (f a))
      ≡⟨ refl ⟩ 
    f a ∎
    where open ≡-Reasoning
  
  ○-identityʳ : {A : Set ℓ} (ma : ○ A) → (ma >>= return) ≡ ma
  ○-identityʳ {A = A} (◎ mta) = cong ◎_ {!!}
    where open ≡-Reasoning
  
  ○-assoc : {A : Set ℓ₁} {B : Set ℓ₂} {C : Set ℓ₃} (ma : ○ A) (f : A → ○ B) (g : B → ○ C)
      → (ma >>= f >>= g) ≡ (ma >>= (λ x → f x >>= g))
  ○-assoc ma f g = {!!}
  -}
