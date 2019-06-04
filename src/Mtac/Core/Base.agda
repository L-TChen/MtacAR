{-# OPTIONS --without-K --safe #-}

module Mtac.Core.Base where 

open import Prelude.Core
open import Reflection.Extended

open import Mtac.Core.Exception

data Tac : Set where
  term    : (`a : Term)                → Tac
  failed  : (tac : String) (`A : Type) → Tac
  error   : (e : Exception)            → Tac 
  -- other types of exceptions, e.g., no matched pattern, abstraction over a non-variable 

-- the following deals with the universe levels.
-- It is problematic if ○ A = TC Tac.
record ○_ (A : Set ℓ) : Set ℓ where
  constructor ◎_
  field
    toTC : TC Tac
open ○_ public

infixr 0 ◎_
infixr 0 ○_

------------------------------------------------------------------------
-- Run a typed tactic

runTT : ○ A → Tactic
runTT {A = A} (◎ ta) hole = do
  `holeTy ← inferType hole
  `A      ← quoteTC A
  unify `holeTy `A          -- first make sure that hole's type is unifible with A.

  ta >>= λ where
    (error e)       → typeError $ strErr "Uncaught exception:" ∷ toErrorPart e
    (failed tac `A) → typeError $ strErr "Fail to find" ∷ termErr `A ∷ strErr ("by " ++ tac) ∷ []
    (term `a)       → unify `a hole

macro
  run  = runTT

------------------------------------------------------------------------
-- Print error message to Agda debug frame with debug id "mtac"
-- See user manual for usage.

print : ℕ → ErrorParts → TC ⊤
print n errs = debugPrint "mtac" n errs

--------------------------------------------------

return○′ : A → TC Tac
return○′ a = quoteTC a >>= return ∘ term 

return○ : A → ○ A
return○ = ◎_ ∘ return○′

unquoteBind : (f : A → ○ B) → Tac → TC Tac
unquoteBind f (term `a) = unquoteTC `a >>= toTC ∘ f
unquoteBind f tac       = return tac

throw′ : Exception → TC Tac
throw′ = return ∘ error

bind○ : ○ A → (A → ○ B) → ○ B
bind○ (◎ `a) f = ◎ `a >>= unquoteBind f

joinTC○ : TC (○ A) → ○ A
joinTC○ ma = ◎ ma >>= toTC

liftTC : TC A → ○ A
liftTC ma = ◎ ma >>= return○′

instance
-- Monad laws are proved in Mtac.Core.MonadLaw
  ○-Monad : Monad ○_
  ○-Monad = record
    { return = return○
    ; _>>=_  = bind○ }

  ○-MonadErr : MonadError Exception ○_
  throw      ⦃ ○-MonadErr ⦄ err      = ◎ return (error err)
  try_catch_ ⦃ ○-MonadErr ⦄ (◎ ta) f = ◎ ta >>= λ where
    (error e) → toTC $ f e
    tac       → return tac

  ○-Applicative : Applicative ○_
  ○-Applicative = monad⇒applicative

  ○-Functor : Functor ○_
  ○-Functor = functor ○-Applicative

  ○-Alternative : Alternative ○_
  _∙_   ⦃ ○-Alternative ⦄ _ _ = _
  empty ⦃ ○-Alternative ⦄ = ◎ return (failed "" unknown)
  _<|>_ ⦃ ○-Alternative ⦄ (◎ ta) (◎ tb) = ◎ ta >>= λ where
    (failed _ _) → tb 
    _            → ta
