{-# OPTIONS --without-K --safe #-}

module Mtac.Core.Base where

open import Prelude
open import Reflection.Extended

open import Mtac.Core.Exception

data Tac : Set where
  term    : (`a : Term)                → Tac
  failed  : (tac : String) (`A : Type) → Tac
  error   : (e : Exception)            → Tac
  -- other types of exceptions, e.g., no matched pattern, abstraction over a non-variable


-- ○ deals with the universe levels.
-- It is problematic if ○ A = TC Tac.
record ○ (A : Set ℓ) : Set ℓ where
  constructor ◎_
  field
    toTC : TC Tac
open ○ public

infixr 0 ◎_

------------------------------------------------------------------------
-- Run a typed tactic

getMetas : Term → List Meta
getMetas = recTerm (record
                      { Pvar         = λ _ → concatMap unArg
                      ; Pcon         = λ _ → concatMap unArg
                      ; Pdef         = λ _ → concatMap unArg
                      ; Plam         = λ _ → unAbs
                      ; Ppat-lam     = λ _ → concatMap unArg
                      ; Ppi          = λ xs ys → unArg xs ++ unAbs ys
                      ; Psort        = λ _ → []
                      ; PsortSet     = λ xs → xs
                      ; PsortLit     = λ _ → []
                      ; PsortUnknown = []
                      ; Plit         = λ _ → []
                      ; Pmeta        = λ x xs → x ∷ concatMap unArg xs
                      ; Punknown     = []
                      ; Pclause      = λ _ _ xs → xs
                      ; PabsClause   = λ _ _ → []
                      })

runTT : ○ A → Term → TC ⊤
runTT {A = A} (◎ ta) hole = do

  `holeTy ← inferType hole
  `A      ← quoteTC A

  debugPrint "mtac" 10 [ strErr "The type of hole has meta variables: " ]
  let metas = getMetas `A
  for metas λ s → debugPrint "mtac" 10 [ strErr (show s) ]

  `holeTy =′ `A          -- check if hole's type is unifible with A.

  caseM ta of λ where
    (error e)       → typeError $ strErr "Uncaught exception:" ∷ toErrorPart e
    (failed tac `A) → typeError $ strErr "Fail to find" ∷ termErr `A ∷ strErr ("by " ++ tac) ∷ []
    (term `a)       → unify hole `a

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
  ○-Monad : Monad ○
  ○-Monad = record
    { return = return○
    ; _>>=_  = bind○ }

  ○-MonadErr : MonadError Exception ○
  throw      ⦃ ○-MonadErr ⦄ err      = ◎ return (error err)
  try_catch_ ⦃ ○-MonadErr ⦄ (◎ ta) f = ◎ caseM ta of λ where
    (error e) → toTC (f e)
    tac       → return tac

  ○-Applicative : Applicative ○
  ○-Applicative = Monad⇒Applicative {○} ⦃ ○-Monad ⦄

  ○-Functor : Functor ○
  ○-Functor = Applicative⇒Functor

  ○-Alternative : Alternative ○
  _∙_   ⦃ ○-Alternative ⦄ tt tt = tt
  empty ⦃ ○-Alternative ⦄ = ◎ return (failed "" unknown)
  _<|>_ ⦃ ○-Alternative ⦄ (◎ ta) (◎ tb) = ◎ caseM ta of λ where
    (failed _ _) → tb
    _            → ta
