{-# OPTIONS --safe --without-K #-}

module Reflection.Extended.Free where

open import Prelude.Core
open import Agda.Builtin.Reflection as Builtin
  renaming ( left-assoc  to assocˡ
           ; right-assoc to assocʳ
           ; primQNameFixity to getFixity
           ; arg-info to argInfo
           ; agda-sort to sort
           ; record-type to record′
           ; data-cons   to constructor′
           ; prim-fun    to primitive′ )

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
