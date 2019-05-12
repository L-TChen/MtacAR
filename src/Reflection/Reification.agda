{-# OPTIONS -v 2 #-}

module Reflection.Reification where

open import Prelude hiding (_⟨_⟩_)
open import Data.Fin as F
  using (Fin)
import Data.List as L
open import Agda.Builtin.TrustMe

open import Reflection.Base

infix  2 ○_
infix  0 ◎_
infixl 0 mcase_of_
infix  0 mmatch
infixr 4 Ptele
infixr 4 Pbase
infixr 1 _∣_
infixr 2 ∣_
infix  2 _end

-- to be addressed properly 
Exception        = String
showExcept       = id
NotCanonical     = λ (id : Name) → show id +++ " is not canonical"
NotFound         = "Not Found"
InvalidPattern   = "Invalid Pattern"
EmptyClause      = "Empty Clause"
NoPatternMatched = "No Pattern Matched"
NotImplemented   = "Not Implemented"

-----------------------------------------------
-- A monad for typed tactic programming in Agda

record ○_ (A : Set ℓ) : Set where
  constructor ◎_
  field
    tm : TC (Exception ⊎ Term)
open ○_ public

returnR : A → ○ A
returnR a = ◎ ⦇ inj₂ (quoteTC a) ⦈

bindR : ○ A → (A → ○ B) → ○ B
bindR (◎ ta) f = ◎
  ta >>= λ { (inj₁ err) → return (inj₁ err)
           ; (inj₂ ta)  → bindTC (unquoteTC ta) (tm ∘ f) }

join : TC (○ A) → ○ A
join ma = ◎ (tm <$> ma >>= id)

fromTC : {A : Set ℓ} → TC A → ○ A
fromTC ma = ◎ ma >>=TC λ a → quoteTC a >>= return ∘ inj₂   -- check universe issue here 

instance
  ○-Monad : Monad {ℓ} ○_
  ○-Monad = record
    { return = returnR
    ; _>>=_  = bindR }
    
---------------------------------------------------------------------
-- ○ supports exception handling

  ○-MonadErr : MonadError {ℓ₁ = ℓ} Exception ○_
  ○-MonadErr = record
    { throw      = ◎_ ∘ throw
    ; try_catch_ = λ { (◎ a) handler → ◎ try a catch (tm ∘ handler) }
    }

  ○-Alternative : Alternative {ℓ} ○_
  ○-Alternative = record { azero = ◎ typeError [] ; _<|>_ = λ { (◎ a) (◎ b) → ◎ a <|> b } }
--------------------------------------------------------------------------------
-- Check Agda's implementation

postulate
  identityˡ : {A : Set ℓ} (a : A) (f : A → ○ B) → (return a >>= f) ≡ f a
  --    ◎ ((quoteTC a >>=TC unquoteTC) >>=TC (λ x → tm (f x))) ≡ f a
  identityʳ : {A : Set ℓ} (ma : ○ A) → (ma >>= return) ≡ ma
  --    ◎ ((tm ma >>=TC unquoteTC) >>=TC (λ x → quoteTC x)) ≡ ma
  assoc : {A : Set ℓ} (ma : ○ A) (f : A → ○ B) (g : B → ○ C)
    → (ma >>= f >>= g) ≡ (ma >>= (λ x → f x >>= g))
  --  ◎ (((tm ma >>=TC unquoteTC) >>=TC (λ x → tm (f x))) >>=TC unquoteTC)
  --    >>=TC (λ x → tm (g x)))
  --    ≡
  --  ◎ (tm ma >>=TC unquoteTC) >>=TC
  --       (λ x → (tm (f x) >>=TC unquoteTC) >>=TC (λ x₁ → tm (g x₁))))

------------------------------------------------------------------------
-- EVar in Mtac

evar : (A : Set ℓ) → ○ A
evar A = ◎ inj₂ <$> (quoteTC A >>= newMeta)

isEvar : {A : Set ℓ} → A → ○ Bool
isEvar {A} a = ◎ do
  (meta _ _) ← quoteTC a where _ → inj₂ <$> quoteTC false
  ⦇ inj₂ (quoteTC true) ⦈
------------------------------------------------------------------------
-- Fixpoint operation for recursion

{-# TERMINATING #-}
mfix : (A : Set ℓ) (P : A → Set ℓ′) → ((∀ x → ○ P x) → (∀ x → ○ P x))
  → (x : A) → ○ P x
mfix A P rec x = rec (mfix A P rec) x

------------------------------------------------------------------------
-- Run a typed program

runR : ○ A → Script
runR (◎ ma) hole = do
  inj₂ ta ← ma
    where (inj₁ err) → typeError [ strErr (showExcept err) ]    
  unify ta hole
  
macro
  Proof_∎ = runR
  run     = runR
------------------------------------------------------------------------
-- Misc 

apply : {A B : Set ℓ} → (A → B) → ○ A → ○ B
apply = _<$>_ 

print : ℕ → ErrorParts → TC ⊤
print n errs = debugPrint "mtact" n errs

mprint : ℕ → ErrorParts → ○ ⊤
mprint n errs = fromTC $ print n errs

mprintStr : String → ○ ⊤
mprintStr str = mprint 0 [ strErr str ]
------------------------------------------------------------------------
-- meta-pattern match

data Patt (A : Set ℓ) (P : A → Set ℓ′) : Set (lsuc ℓ ⊔ ℓ′) where
  Pbase : (x : A)     → (px : ○ P x)   → Patt A P
  Ptele : {C : Set ℓ} → (C → Patt A P) → Patt A P

Patts : (A : Set ℓ) (P : A → Set ℓ′) → ℕ → Set (lsuc ℓ ⊔ ℓ′)
Patts A P n = Vec (Patt A P) (suc n)

------------------------------------------------------------------------
-- Check if the LHS is unifiable with qa

check : Term → List Meta → Term → TC Term
check qa metaCxt t@(con (quote Pbase) (_ ∷ _ ∷ _ ∷ _ ∷ vArg qlhs ∷ vArg qrhs ∷ [])) = do
  print 2 $ strErr "Pbase matched against" ∷ [] -- ∷ termErr t ∷ []
  let qlhs' = varsToMetas metaCxt qlhs
  let qrhs' = varsToMetas metaCxt qrhs

--  print 2 $ strErr "Check" ∷ termErr qa ∷ strErr "against" ∷ termErr qlhs' ∷ strErr "with RHS: " ∷ termErr qrhs' ∷ []
  unify qa qlhs'
--  print 2 $ termErr qa ∷ strErr "is unifiable with" ∷ termErr qlhs' ∷ []  

  return qrhs'
  
check qa metaCxt (con (quote Ptele) (_ ∷ _ ∷ _ ∷ _ ∷ hArg qA ∷ vArg (vLam s t) ∷ [])) = do
  (meta x args) ← newMeta qA where _ → typeError [ strErr "Not reachable" ]
  
  print 2 $ strErr "Metavar:" ∷ termErr (meta x args) ∷ strErr "of type" ∷ termErr qA ∷ strErr "generated" ∷ []
  check qa (x ∷ metaCxt) t
  
check _ _ t = do
--  print 2 $ strErr "Failed to match" ∷ termErr t ∷ []
  typeError $ strErr "Invalid pattern:" ∷ termErr t ∷ []

------------------------------------------------------------------------
-- 

mmatchOne : (P : A → Set ℓ) → Term → Patt A P → TC Term
mmatchOne P qa pat = do
--  cxt ← getContext
--  print 10 $ strErr "Context:" ∷ 
--    concatMap (λ { (arg i x) → strErr "\t" ∷ strErr (show i) ∷ termErr x ∷ [] }) cxt
  qpat ← quoteTC pat
  print 2 $ strErr "Pattern to check" ∷ termErr qpat ∷ []
  
  check qa [] qpat
  
mmatch : (P : ∀ A → Set ℓ) (a : A) → Patts A P n → ○ P a
mmatch {A = A} P a patts = (join $ quoteTC a >>= go patts >>= unquoteTC) <|> throw NoPatternMatched
  where
    go : Patts A P n → Term → TC Term
    go (x ∷ [])         qt = mmatchOne P qt x
    go (x ∷ xs@(_ ∷ _)) qt = mmatchOne P qt x <|> go xs qt

------------------------------------------------------------------------
-- Syntax sugar

syntax mfix A (λ x → e) (λ f → t) = mfix f ∶⟨ x ∶ A ⟩⇒ e ≔ t 
syntax Pbase x b = x ⇒ b
syntax Ptele (λ x → e) = x :> e
syntax mmatch (λ x → τ) a pats = mcase a ∶ x ⇒ τ of pats
infix 0 mfix

mcase_of_ : {P : ∀ A → Set ℓ} (a : A) → Patts A P n → ○ P a
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
tauto = mfix f ∶⟨ x ∶ Set ⟩⇒ x ≔
 λ x →
  mcase x of
    ∣ ⊤ ⇒ return tt
    ∣ p₁ :> p₂ :> (p₁ × p₂) ⇒ ⦇ f p₁ , f p₂ ⦈
    ∣ p₁ :> p₂ :> (p₁ ⊎ p₂) ⇒
      try     (f p₁ >>= return ∘ inj₁)
      finally (f p₂ >>= return ∘ inj₂)
    ∣ p :> p ⇒ throw NotFound
  end 

{-# TERMINATING #-}
tauto2 : (P : Set) → ○ P
tauto2 P = 
  mcase P of
    ∣ ⊤ ⇒ return tt
    ∣ p₁ :> p₂ :> (p₁ × p₂) ⇒ ⦇ tauto2 p₁ , tauto2 p₂ ⦈
    ∣ p₁ :> p₂ :> (p₁ ⊎ p₂) ⇒
      try     (tauto2 p₁ >>= return ∘ inj₁)
      finally (tauto2 p₂ >>= return ∘ inj₂)
    ∣ p :> p ⇒ throw NotFound
  end
  
g : ⊤
g = Proof (tauto2 $ ⊤) ∎

-------------------------------------------------------------------------------
-- Typed Back-Tracking Tactic Monad 

-- data Goal : Set₁ where
--   MV     : {A : Set} → A → Goal
--   AHyp   : {A : Set} → (A → Goal) → Goal
--   HypRem : {A : Set} → A → Goal → Goal

-- Goals : Set₁
-- Goals = List Goal
