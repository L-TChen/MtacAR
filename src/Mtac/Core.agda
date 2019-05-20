{-# OPTIONS --without-K --safe #-}

module Mtac.Core where

open import Prelude hiding (_⟨_⟩_)
open import Reflection.Extended

open import Mtac.Core.Exception public
-----------------------------------------------
-- A monad for typed tactic programming in Agda

data Tac       : Set
record ○_ (A : Set ℓ) : Set ℓ 

record ○_ A where
  constructor ◎_
  field
    toTC : TC Tac
open ○_ public

infix 0 ◎_
infix 0 ○_

data Tac where
  term    : (`a : Term)     → Tac
  blocked : (msg : String)  → Tac  -- for testing only 
  error   : (e : Exception) → Tac
  
------------------------------------------------------------------------
-- Run a typed tactic

runTT : ○ A → Tactic
runTT {A = A} (◎ ta) hole = do
  term `a ← ta
    where
      error e     → typeError $ strErr "Uncaught exception:" ∷ strErr (show e) ∷ []
      blocked msg → typeError $ strErr "Tactic is blocked:" ∷ strErr msg ∷ []
  `A ← quoteTC A
  unify `a hole

macro
  run  = runTT

--------------------------------------------------

print : ℕ → ErrorParts → TC ⊤
print n errs = debugPrint "mtac" n errs

returnR : A → ○ A
returnR a = ◎ quoteTC a >>= λ t → return $ term t

unquoteBind : (f : A → ○ B) → Tac → TC Tac
unquoteBind f (term `a)     = unquoteTC `a >>= toTC ∘ f 
unquoteBind f b@(blocked _) = return b
unquoteBind f t@(error x)   = return t

bindR : ○ A → (A → ○ B) → ○ B
bindR (◎ `a) f = ◎ `a >>= unquoteBind f

joinR : TC (○ A) → ○ A -- TC Tac
joinR ma = ◎ ma >>= toTC

liftTC : TC A → ○ A
liftTC ma = ◎ ma >>= quoteTC >>= return ∘ term

instance
  ○-Monad : Monad ○_
  ○-Monad = record
    { return = returnR
    ; _>>=_  = bindR }

  ○-MonadErr : MonadError Exception ○_
  throw      ⦃ ○-MonadErr ⦄ err    = ◎ return (error err)
  try_catch_ ⦃ ○-MonadErr ⦄ (◎ ta) f = ◎ ta >>= λ
    { b@(blocked _) → return b
    ; (error e)     → toTC $ f e
    ; ta@(term `a)  → return ta }

  ○-MonadFail : MonadFail ○_
  fail ⦃ ○-MonadFail ⦄ msg = ◎ return (blocked msg)
    
  ○-Applicative : Applicative ○_
  ○-Applicative = monad⇒applicative

  ○-Alternative : Alternative ○_
  ○-Alternative = record { azero = ◎ typeError [] ; _<|>_ = λ { (◎ a) (◎ b) → ◎ a <|> b } }
