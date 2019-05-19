{-# OPTIONS --without-K --safe #-}

module Mtac.Core where

open import Prelude hiding (_⟨_⟩_)

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

print : ℕ → ErrorParts → TC ⊤
print n errs = debugPrint "mtac" n errs

returnR : A → ○ A
returnR a = ◎ quoteTC a >>= λ t → return (inj₂ t)

quoteBind : (f : A → ○ B) → Exception ⊎ Term → TC (Exception ⊎ Term)
quoteBind f (inj₁ err) = returnTC (inj₁ err)
quoteBind f (inj₂ qa)  = (unquoteTC qa >>= toTC ∘ f) << print 40 (termErr qa ∷ [])

bindR : ○ A → (A → ○ B) → ○ B
bindR (◎ ta) f = ◎ ta >>= (quoteBind f)

joinR : TC (○ A) → ○ A
joinR ma = ◎ ma >>= (return ∘ toTC) >>= id

fromTC : TC A → ○ A
fromTC ma = ◎ ma >>= λ a → quoteTC a >>= return ∘ inj₂

instance
  ○-Monad : Monad ○_
  ○-Monad = record
    { return = returnR
    ; _>>=_  = bindR }

  ○-MonadExcept : MonadError Exception ○_
  throw      ⦃ ○-MonadExcept ⦄ err     = ◎ (return $ inj₁ err)
  try_catch_ ⦃ ○-MonadExcept ⦄ (◎ ta) f = ◎ do
    (inj₂ t) ← ta
      where (inj₁ err) → toTC $ f err
    return $ inj₂ t
    
  ○-Applicative : Applicative ○_
  ○-Applicative = monad⇒applicative

  ○-Alternative : Alternative ○_
  ○-Alternative = record { azero = ◎ typeError [] ; _<|>_ = λ { (◎ a) (◎ b) → ◎ a <|> b } }

------------------------------------------------------------------------
-- Run a typed tactic

runTT : ○ A → Tactic
runTT {A = A} (◎ ma) hole = do
  inj₂ `a ← ma   where (inj₁ err) → typeError [ strErr (showExcept err) ]
  `A ← quoteTC A
--  checkedHole ← checkType hole `A
  unify `a hole
  
macro
  run  = runTT
