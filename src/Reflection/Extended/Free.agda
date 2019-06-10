{-# OPTIONS --safe --without-K #-}

module Reflection.Extended.Free where

open import Prelude
open import Reflection.Extended.Base

record TermRec {A B C : Set} : Set where
  field
    Pvar : ℕ → List (Arg A) → A
    Pcon : Name → List (Arg A) → A
    Pdef : Name → List (Arg A) → A
    Plam : Visibility → Abs A → A
    Ppat-lam : List B → List (Arg A) → A
    Ppi      : Arg A → Abs A → A
    Psort : C → A
    PsortSet : A → C
    PsortLit : ℕ → C
    PsortUnknown : C
    Plit  : Literal → A
    Pmeta : Meta → List (Arg A) → A
    Punknown : A
    Pclause : List (Arg Pattern) → A → B
    PabsClause : List (Arg Pattern) → B -- where
  mutual
    recArg : Arg Term → Arg A
    recArg (arg i x) = arg i (recTerm x)

    recArgs : List (Arg Term) → List (Arg A)
    recArgs [] = []
    recArgs (t ∷ ts) = recArg t ∷ recArgs ts

    recAbs : Abs Term → Abs A
    recAbs (abs s t) = abs s (recTerm t)

    recClause : Clause → B
    recClause (clause ps t)      = Pclause ps (recTerm t)
    recClause (absurd-clause ps) = PabsClause ps

    recClauses : List Clause → List B
    recClauses [] = []
    recClauses (c ∷ cs) = recClause c ∷ recClauses cs

    recSort : Sort → C
    recSort (set t) = PsortSet (recTerm t)
    recSort (lit n) = PsortLit n
    recSort unknown = PsortUnknown

    recTerm : Term → A
    recTerm (var x args) = Pvar x (recArgs args)
    recTerm (con c args) = Pcon c (recArgs args)
    recTerm (def f args) = Pdef f (recArgs args)
    recTerm (lam v t) = Plam v (recAbs t)
    recTerm (pat-lam cs args) = Ppat-lam (recClauses cs) (recArgs args)
    recTerm (pi a b) = Ppi (recArg a) (recAbs b)
    recTerm (sort s) = Psort (recSort s)
    recTerm (lit l) = Plit l
    recTerm (meta x args) = Pmeta x (recArgs args)
    recTerm unknown = Punknown
open TermRec public
  using (recTerm; recSort; recClauses)

idRec : TermRec {A → Term} {A → Clause} {A → Sort}
idRec = record
  { Pvar = λ n args a  → var n  $ map (a |>_) <$> args
  ; Pcon = λ id args a → con id $ map (a |>_) <$> args
  ; Pdef = λ id args a → def id $ map (a |>_) <$> args
  ; Plam = λ {v t a → lam v ((a |>_) <$> t) }
  ; Ppat-lam = λ cs args a → pat-lam ((_$ a) <$> cs) ((λ { (arg i x) → arg i (x a) }) <$> args)
  ; Ppi      = λ { (arg i x) (abs s t) a → pi (arg i (x a)) (abs s (t a)) }
  ; Psort    = λ { s a → sort (s a) }
  ; PsortSet = λ t a → set (t a)
  ; PsortLit = λ n _ → lit n
  ; PsortUnknown = λ _ → unknown
  ; Plit     = λ l a → lit l
  ; Pmeta    = λ x args a → meta x ((λ { (arg i x) → arg i (x a) }) <$> args)
  ; Punknown = λ _ → unknown
  ; Pclause    = λ ps t a → ps ↦ t a
  ; PabsClause = λ ps a → absurd-clause ps
  }

anyTermRec : TermRec {A → Bool} {⊤} {⊤}
anyTermRec = record
  { Pvar     = λ _ args a → any ((_$ a) ∘ unArg) args
  ; Pcon     = λ _ args a → any ((_$ a) ∘ unArg) args
  ; Pdef     = λ _ args a → any ((_$ a) ∘ unArg) args
  ; Plam     = λ _ → unAbs ; Ppat-lam = λ _ args a → any ((_$ a) ∘ unArg) args
  ; Ppi      = λ dom cod a → unArg dom a || unAbs cod a
  ; Psort    = λ _ _ → false ; PsortSet = λ _ → _ ; PsortLit = λ _ → _ ; PsortUnknown = _
  ; Plit         = λ _ _ → false
  ; Pmeta        = λ _ args a → any ((_$ a) ∘ unArg) args ; Punknown     = λ _ → false
  ; Pclause      = λ _ _ → _ ; PabsClause   = λ _ → _
  }
