{-# OPTIONS --type-in-type #-}

module Mtac.Construct where

open import Prelude
open import Mtac.Core
open import Reflection.Extended

------------------------------------------------------------------------
-- EVar in Mtac

evar : (A : Set) → ○ A
evar A = ◎ inj₂ <$> (quoteTC A TC.>>= newMeta)

------------------------------------------------------------------------
-- Fixpoint operation for recursion

{-# TERMINATING #-}
mfix : (A : Set) (P : A → Set) → ((∀ x → ○ P x) → (∀ x → ○ P x))
  → (x : A) → ○ P x
mfix A P rec = rec (mfix A P rec)

------------------------------------------------------------------------
-- Datatype for meta-pattern match 

data Patt (A : Set) (P : A → Set) : Set where
  Pbase : (x : A)   (px : ○ P x)   → Patt A P
  Ptele : (C : Set) (f : C → Patt A P) → Patt A P

Patts : (A : Set) (P : A → Set) → ℕ → Set
Patts A P n = Vec (Patt A P) (suc n)

split : {P : A → Set} → Patt A P → TC (Term × Term)
split pat = do
  data-type n _ ← getDefinition (quote Patt)
    where t → print 5 (strErr "Impossible case reached:" ∷ termErr {!!} ∷ []) >> azero
  (con id args) ← quoteTC pat
    where t → (print 20 $ strErr "Invalid pattern" ∷ termErr t ∷ []) >> azero
  go [] (con id (drop n args))
  where
    go : Metas → Term → TC (Term × Term)
    go metas (con (quote Pbase) (vArg qLhs ∷ vArg qRhs ∷ []))       = {!drop !}
    go metas (con (quote Ptele) (vArg qC   ∷ vArg (vLam s t) ∷ [])) = {!!}
    go _ _ = {!!}
------------------------------------------------------------------------
-- Check if the LHS is unifiable with qa
patt1 = quoteTerm (Pbase {P = λ (x : Set) → x } ⊤ (return tt))
patt2 = quoteTerm (Ptele {P = λ (x : Set) → x } Set λ x → Pbase ⊤ (return tt))

check : Term → List Meta → Term → TC Term
check qa metaCxt t@(con (quote Pbase) (_ ∷ _ ∷ vArg qlhs ∷ vArg qrhs ∷ [])) = do
  let qlhs' = varsToMetas metaCxt qlhs
  let qrhs' = varsToMetas metaCxt qrhs
  unify qlhs' qa
  print 20 $ termErr qa ∷ strErr "is unified with" ∷ termErr qlhs' ∷ []
  return qrhs'
  
check qa metaCxt (con (quote Ptele) (_ ∷ _ ∷ vArg qA ∷ vArg (vLam s t) ∷ [])) = do
  (meta x args) ← newMeta qA
    where _ → (print 20 $ [ strErr "New meta has args?" ]) >> azero
  print 10 $ strErr "Metavar:" ∷ termErr (meta x args)
    ∷ strErr "of type" ∷ termErr qA ∷ strErr "generated" ∷ []
  check qa (x ∷ metaCxt) t
  
check _ _ t = (print 20 $ strErr "Invalid pattern" ∷ termErr t ∷ []) >> azero

------------------------------------------------------------------------
-- 

mmatchOne : (P : A → Set) → Term → Patt A P → TC Term
mmatchOne P qa pat = do
  qpat ← quoteTC pat
  print 10 $ strErr "Checking:  " ∷ termErr qpat ∷ strErr "\n    with:" ∷ termErr qa ∷ []
  check qa [] qpat
  
mmatch : (P : ∀ A → Set) (a : A) → Patts A P n → ○ P a
mmatch {A} P a patts =
  (joinR $ quoteTC a TC.>>= go patts TC.>>= unquoteTC) <|> throw NoPatternMatched
  where
    go : Patts A P n → Term → TC Term
    go (x ∷ [])         qt = mmatchOne P qt x
    go (x ∷ xs@(_ ∷ _)) qt = mmatchOne P qt x <|> go xs qt
