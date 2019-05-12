module Reflection.Recursion where

open import Prelude 
open import Data.List.Relation.Unary.All

Parg : {A : Set} (P : A → Set) → Arg A → Set
Parg P (arg i a) = P a

Pabs : {A : Set} (P : A → Set) → Abs A → Set
Pabs P (abs s a) = P a

module _ {P : Term → Set} {Q : Clause → Set} {R : Sort → Set}
  (Pvar : (n : ℕ) → {args : Args Term} → All (Parg P) args → P (var n args))
  (Pcon : (c : Name) → {args : Args Term} → All (Parg P) args → P (con c args))
  (Pdef : (f : Name) → {args : Args Term} → All (Parg P) args → P (def f args))
  (Plam : (v : Visibility) {t : Abs Term} → Pabs P t → P (lam v t))
  (Ppat-lam : {cs : Clauses} → All Q cs → {args : Args Term} → All (Parg P) args → P (pat-lam cs args))
  (Ppi : {a : Arg Type} → (Parg P) a → {b : Abs Type} → (Pabs P) b → P (pi a b))
  (Psort : {s : Sort} → R s → P (sort s))
  (PsortSet : {t : Term} → P t → R (set t))
  (PsortLit : (n : ℕ) → R (lit n))
  (PsortUnknown : R unknown)
  (Plit : (l : Literal) → P (lit l))
  (Pmeta : (x : Meta) {args : Args Term} → All (Parg P) args → P (meta x args))
  (Punknown : P unknown)
  (Pclause : (ps : Args Pattern) → {t : Term} → P t → Q (clause ps t))
  (PabsClause : (ps : Args Pattern) → Q (absurd-clause ps))
  where
    open List
    mutual
      elimAbs : (t : Abs Term) → Pabs P t
      elimAbs (abs s x) = elimTerm x -- abs s (elimTerm x)
    
      elimArg : (t : Arg Term) → Parg P t
      elimArg (arg i x) = elimTerm x
        
      elimArgs : (args : Args Term) → All (Parg P) args
      elimArgs [] = []
      elimArgs (x ∷ args) = elimArg x ∷ elimArgs args
    
      elimClause : (c : Clause) → Q c
      elimClause (clause ps t)      = Pclause ps (elimTerm t)
      elimClause (absurd-clause ps) = PabsClause ps
    
      elimClauses : (cs : Clauses) → All Q cs
      elimClauses [] = []
      elimClauses (x ∷ cls) = elimClause x ∷ elimClauses cls
    
      elimSort : (s : Sort) → R s
      elimSort (set t) =
        PsortSet (elimTerm t)
      elimSort (lit n) = PsortLit n
      elimSort unknown = PsortUnknown
      
      elimTerm : (t : Term) → P t
      elimTerm (var x args) = Pvar x (elimArgs args)
      elimTerm (con c args) = Pcon c (elimArgs args)
      elimTerm (def f args) = Pdef f (elimArgs args)
      elimTerm (lam v t) = Plam v (elimAbs t)
      elimTerm (pat-lam cs args) = Ppat-lam (elimClauses cs) (elimArgs args)
      elimTerm (pi a b) = Ppi (elimArg a) (elimAbs b)
      elimTerm (sort s) = Psort (elimSort s)
      elimTerm (lit l) = Plit l
      elimTerm (meta x args) = Pmeta x (elimArgs args)
      elimTerm unknown = Punknown
  
module _
  {A B C : Set}
  (Pvar : ℕ → Args A → A)
  (Pcon : Name → Args A → A)
  (Pdef : Name → Args A → A)
  (Plam : Visibility → Abs A → A)
  (Ppat-lam : List B → Args A → A)
  (Ppi      : Arg A → Abs A → A)
  (Psort : C → A)
  (PsortSet : A → C)
  (PsortLit : ℕ → C)
  (PsortUnknown : C)
  (Plit  : Literal → A)
  (Pmeta : Meta → Args A → A)
  (Punknown : A)
  (Pclause : Args Pattern → A → B)
  (PabsClause : Args Pattern → B) where
  mutual
    recArg : Arg Term → Arg A
    recArg (arg i x) = arg i (recTerm x)

    recArgs : Args Term → List (Arg A)
    recArgs [] = []
    recArgs (t ∷ ts) = recArg t ∷ recArgs ts
    
    recAbs : Abs Term → Abs A
    recAbs (abs s t) = abs s (recTerm t)

    recClause : Clause → B
    recClause (clause ps t)      = Pclause ps (recTerm t)
    recClause (absurd-clause ps) = PabsClause ps

    recClauses : Clauses → List B
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

shiftVar : ℕ → ℕ → Args Term → Term
shiftVar n x args = var (n + x) args
shift : ℕ → Term → Term
shift n = recTerm (shiftVar n) con def lam pat-lam pi sort set lit unknown lit meta unknown clause absurd-clause

shiftArg : ℕ → Arg Term → Arg Term
shiftArg n = recArg (shiftVar n) con def lam pat-lam pi sort set lit unknown lit meta unknown clause absurd-clause

shiftClause : ℕ → Clause → Clause
shiftClause n = recClause (shiftVar n) con def lam pat-lam pi sort set lit unknown lit meta unknown clause absurd-clause

shiftSort : ℕ → Sort → Sort
shiftSort n = recSort (shiftVar n) con def lam pat-lam pi sort set lit unknown lit meta unknown clause absurd-clause

-- mutual
--   shiftArg : ℕ → ℕ → Arg Term → Arg Term
--   shiftArg c d (arg i x) = arg i (shift c d x)

--   shiftArgs : ℕ → ℕ → Args Term → Args Term
--   shiftArgs c d [] = []
--   shiftArgs c d (a ∷ args) = shiftArg c d a ∷ shiftArgs c d args 

--   shiftClause : ℕ → ℕ → Clause → Clause
--   shiftClause c d (clause ps t)      = clause ps (shift c d t)
--   shiftClause c d (absurd-clause ps) = absurd-clause ps

--   shiftClauses : ℕ → ℕ → Clauses → Clauses
--   shiftClauses c d []        = []
--   shiftClauses c d (x ∷ cls) = shiftClause c d x ∷ shiftClauses c d cls

--   shiftAbs : ℕ → ℕ → Abs Term → Abs Term
--   shiftAbs c d (abs s x) = abs s (shift c d x)

--   shiftSort : ℕ → ℕ → Sort → Sort
--   shiftSort c d (set t) = set (shift c d t)
--   shiftSort c d (lit n) = lit n
--   shiftSort c d unknown = unknown

--   shift : ℕ → ℕ → Term → Term
--   shift c d (var x args) = var (d + x) (shiftArgs c d args) --with c ≤? x 
-- --  shift c d (var x args) | yes p = var (d + x) (shiftArgs c d args)
-- --  shift c d (var x args) | no ¬p = var x       (shiftArgs c d args)
--   shift c d (con c₁ args)     = con c₁ (shiftArgs c d args)
--   shift c d (def f args)      = def f  (shiftArgs c d args)
--   shift c d (lam v t)         = lam v (shiftAbs c d t)
--   shift c d (pat-lam cs args) = pat-lam (shiftClauses c d cs) (shiftArgs c d args)
--   shift c d (pi a b)          = pi (shiftArg c d a) (shiftAbs c d b)
--   shift c d (sort s)          = sort (shiftSort c d s)
--   shift c d (lit l)           = lit l
--   shift c d (meta x args)     = meta x (shiftArgs c d args)
--   shift c d unknown           = unknown

-- shift₀ : ℕ → Term → Term
-- shift₀ d = shift 0 d

-- shiftArg₀ = λ d → shiftArg 0 d

-- lem : ∀ n t → shift 0 n t ≡ shift′ 0 n t
-- lem n t = elimTerm
--   {P = λ t → shift 0 n t ≡ shift′ 0 n t}
--   {Q = λ c → shiftClause 0 n c ≡ shiftClause′ 0 n c}
--   {R = λ s → shiftSort 0 n s ≡ shiftSort′ 0 n s}
--   (λ k Pxs → cong (var (n + k)) {!!} ) {!!} {!!} (λ {v {abs s t} Pt → cong (lam v) (cong (abs s) Pt)}) {!!} {!!} {!!} {!!} {!!} {!!} {!!} {!!} {!!} {!!} {!!} t
  
-- module Scoped where
--   variable
--     n m : ℕ
    
--   open R hiding (Clause; Sort)
  
--   data Pat (n : ℕ) : Set where
--     con    : (c : Name) (ps : Args (Pat n)) → Pat n
--     dot    : Pat n
--     var    : (m≡1+n : m ≡ suc n) → (s : String)  → Pat n
--     lit    : (l : Literal) → Pat n
--     proj   : (f : Name)    → Pat n
--     absurd : Pat n

--   data Tm ℕ : Set
--   data Clause ℕ : Set
--   data Sort ℕ : Set
--   Ty : ℕ → Set
--   Ty = Tm

--   data Tm n where
--     var       : (x : Fin n) (args : Args (Tm n)) → Tm n
--     con       : (c : Name)  (args : Args (Tm n)) → Tm n
--     def       : (f : Name)  (args : Args (Tm n)) → Tm n
--     lam       : (v : Visibility) (t : Abs (Tm (suc n))) → Tm n
--     pat-lam   : (cs : List (Clause n)) (args : Args (Tm n)) → Tm n
--     pi        : (a : Arg (Ty n)) (b : Abs (Ty n)) → Tm n
--     sort      : (s : Sort n) → Tm n
--     lit       : (l : Literal) → Tm n
--     meta      : (x : Meta) → Args (Tm n) → Tm n
--     unknown   : Tm n

--   data Clause n where
--     clause        : (ps : Args (Pat n)) (t : Tm n) → Clause n
--     absurd-clause : (ps : Args (Pat n)) → Clause n

--   data Sort n where
--     set     : (t : Tm n) → Sort n
--     lit     : (m : ℕ) → Sort n
--     unknown : Sort n

--   mutual
--     toArgTerm : Arg (Tm n) → Arg Term
--     toArgTerm (arg i x) = arg i (toTerm x)
    
--     toArgsTerm : Args (Tm n) → Args Term
--     toArgsTerm [] = []
--     toArgsTerm (arg i x ∷ args) = arg i (toTerm x) ∷ toArgsTerm args

--     toClause : Clause n → R.Clause
--     toClause (clause ps t) = clause (toArgsPattern ps) (toTerm t)
--     toClause (absurd-clause ps) = absurd-clause (toArgsPattern ps)

--     toClauses : List (Clause n) → R.Clauses
--     toClauses [] = []
--     toClauses (x ∷ cls) = toClause x ∷ toClauses cls
    
--     toTerm : Tm n → R.Term
--     toTerm (var x args) = var (toℕ x) (toArgsTerm args)
--     toTerm (con c args) = con c (toArgsTerm args)
--     toTerm (def f args) = def f (toArgsTerm args)
--     toTerm (lam v (abs s x)) = lam v (abs s (toTerm x))
--     toTerm (pat-lam cs args) = pat-lam (toClauses cs) (toArgsTerm args)
--     toTerm (pi a (abs s x)) = pi (toArgTerm a) (abs s (toTerm x))
--     toTerm (sort (set t)) = sort (set (toTerm t))
--     toTerm (sort (lit m)) = sort (lit m)
--     toTerm (sort unknown) = sort unknown
--     toTerm (lit l) = lit l
--     toTerm (meta x args) = meta x (toArgsTerm args)
--     toTerm unknown = unknown

--     toArgsPattern : Args (Pat n) → Args Pattern
--     toArgsPattern [] = []
--     toArgsPattern (arg i x ∷ args) = arg i (toPattern x) ∷ toArgsPattern args
    
--     toPattern : ∀ {n} → Pat n → Pattern
--     toPattern (con c ps) = con c (toArgsPattern ps)
--     toPattern dot = dot
--     toPattern (var refl s) = var s
--     toPattern (lit l) = lit l
--     toPattern (proj f) = proj f
--     toPattern absurd = absurd
--   {-
--   mutual
--     fromTerm : R.Term → Σ ℕ Tm
--   -}
--   -- 
