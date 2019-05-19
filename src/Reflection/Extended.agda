{-
  This module is partly from Ulf's agda-prelude, see https://github.com/UlfNorell/agda-prelude
-}
module Reflection.Extended where

open import Prelude
open import Reflection.DeBruijn

-- Every metaprogram / tactic is of type `Term → TC ⊤`
Tactic : Set
Tactic = Term → TC ⊤

-- Shorthands for List A
Types Metas Terms ErrorParts : Set
Types      = List Type
Metas      = List Meta
Terms      = List Term
ErrorParts = List ErrorPart

set₀ : Type
set₀ = sort (lit 0)

set! : Type
set! = sort unknown

pattern var₀ x         = var x []
pattern var₁ x a       = var x (vArg a ∷ [])
pattern var₂ x a b     = var x (vArg a ∷ vArg b ∷ [])
pattern var₃ x a b c   = var x (vArg a ∷ vArg b ∷ vArg c ∷ [])
pattern var₄ x a b c d = var x (vArg a ∷ vArg b ∷ vArg c ∷ vArg d ∷ [])

pattern con₀ c         = con c []
pattern con₁ c x       = con c (vArg x ∷ [])
pattern con₂ c x y     = con c (vArg x ∷ vArg y ∷ [])
pattern con₃ c x y z   = con c (vArg x ∷ vArg y ∷ vArg z ∷ [])
pattern con₄ c x y z u = con c (vArg x ∷ vArg y ∷ vArg z ∷ vArg u ∷ [])

pattern def₀ f         = def f []
pattern def₁ f x       = def f (vArg x ∷ [])
pattern def₂ f x y     = def f (vArg x ∷ vArg y ∷ [])
pattern def₃ f x y z   = def f (vArg x ∷ vArg y ∷ vArg z ∷ [])
pattern def₄ f x y z u = def f (vArg x ∷ vArg y ∷ vArg z ∷ vArg u ∷ [])
pattern _↦_ ps t = clause ps t
infix 8 _↦_

pattern sortSet t = sort (set t)
pattern sortLit i = sort (lit i)

`λ : Term → Term
`λ b = lam visible (abs "_" b)

infixl 9 _`∘_
_`∘_ : Term → Term → Term
_`∘_ = def₂ (quote _∘_)

infixr -20 _`$_
_`$_ : Term → Term → Term
_`$_ = def₂ (quote _$_)

_:′_ : Term → Type → TC Term
_:′_ = checkType

λ′ : Arg Type → TC A → TC A
λ′ = extendContext

infix 2 _=′_
_=′_ : Term → Term → TC ⊤
_=′_ = unify

macro
  runTC : TC A → Tactic
  runTC t _ = t >> return tt

arity : Term → ℕ
arity (Π[ _ ∶ _ ] b) = 1 + arity b
arity _              = 0

unArg : {A : Set ℓ} → Arg A → A
unArg (arg _ x) = x

getArgInfo : {A : Set ℓ} → Arg A → ArgInfo
getArgInfo (arg i _) = i

unAbs : {A : Set ℓ} → Abs A → A
unAbs (abs _ x) = x

isVisible : {A : Set ℓ} → Arg A → Bool
isVisible (arg (argInfo visible _) _) = true
isVisible _ = false

absurd-lam : Term
absurd-lam = pat-lam (absurd-clause (vArg absurd ∷ []) ∷ []) []

give : Term → Tactic
give v = λ hole → unify hole v

define : Arg Name → Type → List Clause → TC ⊤
define f a cs = declareDef f a >> defineFun (unArg f) cs

newMeta! : TC Term
newMeta! = newMeta unknown

typeErrorS : String → TC A
typeErrorS s = typeError (strErr s ∷ [])

blockOnMeta! : Meta → TC A
blockOnMeta! x = commitTC TC.>>= λ _ → blockOnMeta x

inferNormalisedType : Term → TC Type
inferNormalisedType t = withNormalisation true (inferType t)


forceFun : Type → TC Type
forceFun a = do
  dom ← newMeta set!
  rng ← newMeta set!
  unify a (vΠ[ "_" ∶ dom ] weaken 1 rng) --  (Π dom `→ weaken 1 rng)
  normalise a
inferFunRange : Term → TC Type
inferFunRange hole = unPi =<< forceFun =<< inferType hole where
  unPi : Type → TC Type
  unPi (pi _ (abs _ (meta x _))) = blockOnMeta! x
  unPi (pi _ (abs _ b)) = maybe pure (typeError ( strErr "Must be applied in a non-dependent function position"
                                           ∷ termErr b ∷ [])) $ strengthen 1 b
  unPi x = typeError (strErr "Invalid goal" ∷ termErr x ∷ [])

--- Convenient wrappers ---

-- Zero for non-datatypes
getParameters : Name → TC ℕ
getParameters d =
  caseM getDefinition d of λ
  { (data-type n _) → pure n
  ; _ → pure 0 }

getConstructors : Name → TC (List Name)
getConstructors d =
  caseM getDefinition d of λ
  { (data-type _ cs) → pure cs
  ; (record′ c _) → pure (c ∷ [])
  ; _ → typeError (strErr "Cannot get constructors of non-data or record type" ∷ nameErr d ∷ [])
  }

getClauses : Name → TC Clauses
getClauses d =
  caseM getDefinition d of λ
  { (function cs) → pure cs
  ; _ → typeError (strErr "Cannot get constructors of non-function type" ∷ nameErr d ∷ [])
  }

-- Get the constructor of a record type (or single-constructor data type)
recordConstructor : Name → TC Name
recordConstructor r =
  caseM getConstructors r of λ
  { (c ∷ []) → pure c
  ; _ → typeError $ strErr "Cannot get constructor of non-record type" ∷ nameErr r ∷ [] }

module Free where
  record Rec {A B C : Set} : Set where
    field
      Pvar : ℕ → Args A → A
      Pcon : Name → Args A → A
      Pdef : Name → Args A → A
      Plam : Visibility → Abs A → A
      Ppat-lam : List B → Args A → A
      Ppi      : Arg A → Abs A → A
      Psort : C → A
      PsortSet : A → C
      PsortLit : ℕ → C
      PsortUnknown : C
      Plit  : Literal → A
      Pmeta : Meta → Args A → A
      Punknown : A
      Pclause : Args Pattern → A → B
      PabsClause : Args Pattern → B -- where
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
  open Rec public
    using (recTerm; recSort; recClauses)
    
  idRec : Rec
  idRec = record
    { Pvar = var ; Pcon = con ; Pdef = def ; Plam = lam ; Ppat-lam = pat-lam ; Ppi = pi
    ; Psort = sort ; PsortSet = set ; PsortLit = lit ; PsortUnknown = unknown
    ; Plit = lit ; Pmeta = meta ; Punknown = unknown
    ; Pclause = clause
    ; PabsClause = absurd-clause
    }
  weakRec : ℕ → Rec
  weakRec n = record idRec { Pvar = λ x args → var (n + x) args }

  varToMetaRec : Metas → Rec
  varToMetaRec metaCxt = record idRec { Pvar = metaOrVar }
    where
      metaOrVar : ℕ → Args Term → Term
      metaOrVar n args with metaCxt !! n
      ... | nothing = var n args
      ... | just x  = meta x args
  {-  
  weaken : ℕ → Term → Term
  weaken = recTerm ∘ weakRec
-}
  varsToMetas : List Meta → Term → Term
  varsToMetas = recTerm ∘ varToMetaRec
open Free public

