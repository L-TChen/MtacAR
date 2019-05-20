module Reflection.Free where

open import Agda.Builtin.Reflection as TC
open import Agda.Builtin.List
open import Agda.Builtin.Nat

record Rec {A B C : Set} : Set where
  field
    Pvar : Nat → List (Arg A) → A
    Pcon : Name → List (Arg A) → A
    Pdef : Name → List (Arg A) → A
    Plam : Visibility → Abs A → A
    Ppat-lam : List B → List (Arg A) → A
    Ppi      : Arg A → Abs A → A
    Psort : C → A
    PsortSet : A → C
    PsortLit : Nat → C
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
    recTerm (agda-sort s) = Psort (recSort s)
    recTerm (lit l) = Plit l
    recTerm (meta x args) = Pmeta x (recArgs args)
    recTerm unknown = Punknown
open Rec public
  using (recTerm; recSort; recClauses)

idRec : Rec
idRec = record
  { Pvar = var ; Pcon = con ; Pdef = def ; Plam = lam ; Ppat-lam = pat-lam ; Ppi = pi
  ; Psort = agda-sort ; PsortSet = set ; PsortLit = lit ; PsortUnknown = unknown
  ; Plit = lit ; Pmeta = meta ; Punknown = unknown
  ; Pclause = clause
  ; PabsClause = absurd-clause
  }
