{-# OPTIONS --without-K --safe #-}

-- Code inspired by or copied from Ulf Norell's agda-prelude https://github.com/UlfNorell/agda-prelude

module Reflection.Extended.Base where

open import Prelude

import Agda.Builtin.Reflection as Builtin
module TC = Builtin
open TC public
  renaming ( left-assoc  to assocˡ
           ; right-assoc to assocʳ
           ; primQNameFixity to getFixity
           ; arg-info to argInfo
           ; agda-sort to sort
           ; record-type to record′
           ; data-cons   to constructor′
           ; prim-fun    to primitive′
           ; instance′   to inst)

pattern relevant′₀         = modality relevant quantity-0
pattern relevant′ω         = modality relevant quantity-ω
pattern visible′           = argInfo visible   relevant′ω
pattern hidden′            = argInfo hidden    relevant′ω
pattern instance′          = argInfo inst      relevant′ω
pattern vArg ty            = arg visible′  ty
pattern hArg ty            = arg hidden′   ty
pattern iArg ty            = arg instance′ ty
pattern vLam s t           = lam visible   (abs s t)
pattern hLam s t           = lam hidden    (abs s t)
pattern iLam s t           = lam inst      (abs s t)
pattern absurd-lam = pat-lam (absurd-clause (vArg absurd ∷ []) ∷ []) []

pattern Π[_∶_]_  s a ty    = pi a (abs s ty)
pattern vΠ[_∶_]_ s a ty    = Π[ s ∶ (vArg a) ] ty
pattern hΠ[_∶_]_ s a ty    = Π[ s ∶ (hArg a) ] ty
pattern iΠ[_∶_]_ s a ty    = Π[ s ∶ (iArg a) ] ty

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
pattern ⟨_,_⟩↦_ tel ps t = clause tel ps t
infix 8 ⟨_,_⟩↦_

pattern sortSet t = sort (set t)
pattern sortLit i = sort (lit i)

pattern set₀ = sort (lit 0)
pattern set₁ = sort (lit 1)
pattern set! = sort unknown

instance
  NameEq : Eq Name
  _==_ ⦃ NameEq ⦄ = TC.primQNameEquality
  NameShow : Show Name
  show ⦃ NameShow ⦄ = TC.primShowQName
  MetaEq : Eq Meta
  _==_ ⦃ MetaEq ⦄ = TC.primMetaEquality
  MetaShow : Show Meta
  show ⦃ MetaShow ⦄ = TC.primShowMeta
  LitShow : Show Literal
  show ⦃ LitShow ⦄ (nat n)    = show n
  show ⦃ LitShow ⦄ (word64 n) = show n
  show ⦃ LitShow ⦄ (float x)  = show x
  show ⦃ LitShow ⦄ (char c)   = show c
  show ⦃ LitShow ⦄ (string s) = show s
  show ⦃ LitShow ⦄ (name x)   = show x
  show ⦃ LitShow ⦄ (meta x)   = show x

  VisibilityShow : Show Visibility
  VisibilityShow = record
    { show = λ
      { visible → "Explicit"
      ; hidden  → "Implicit"
      ; inst    → "Instance" } }

  QuantitiyShow : Show Quantity
  show ⦃ QuantitiyShow ⦄ quantity-0 = "quantity-0"
  show ⦃ QuantitiyShow ⦄ quantity-ω = "quantity-ω"

  RelevanceShow : Show Relevance
  show ⦃ RelevanceShow ⦄ relevant   = "relevant"
  show ⦃ RelevanceShow ⦄ irrelevant = "irrelevant"

  ArgInfoShow : Show ArgInfo
  show ⦃ ArgInfoShow ⦄ (argInfo v (modality r q)) =
    show v ++ " " ++ show r ++ " " ++ show q ++ " arg"

  TCM : Monad TC
  return ⦃ TCM ⦄ = returnTC
  _>>=_  ⦃ TCM ⦄ = bindTC

  TCA : Applicative TC
  TCA = Monad⇒Applicative {TC} ⦃ TCM ⦄

  TCAlter : Alternative TC
  empty ⦃ TCAlter ⦄ = typeError []
  _<|>_ ⦃ TCAlter ⦄ = catchTC
  _∙_   ⦃ TCAlter ⦄ = λ _ _ → _

  TCFunctor : Functor TC
  TCFunctor = Applicative⇒Functor

  FunctorArg : Functor Arg
  _<$>_ ⦃ FunctorArg ⦄ f (arg i x) = arg i (f x)
  FunctorAbs : Functor Abs
  _<$>_ ⦃ FunctorAbs ⦄ f (abs s t) = abs s (f t)

  TraversableArg : Traversable Arg
  traverse ⦃ TraversableArg ⦄ f (arg i x) = ⦇ (arg i) (f x) ⦈
  TraversableAbs : Traversable Abs
  traverse ⦃ TraversableAbs ⦄ f (abs s x) = ⦇ (abs s) (f x) ⦈

Args : (A : Set) → Set
Args A = List (Arg A)

Types Metas Terms ErrorParts Names Clauses Cxt : Set
Types      = List Type
Metas      = List Meta
Terms      = List Term
ErrorParts = List ErrorPart
Names      = List Name
Clauses    = List Clause
Cxt        = Args Type
Telescope  = List (String × Arg Type)

visibility : ArgInfo → Visibility
visibility (argInfo v _) = v

relevance : ArgInfo → Relevance
relevance (argInfo _ (modality r _)) = r

quantity : ArgInfo → Quantity
quantity (argInfo _ (modality _ q)) = q

unArg : Arg A → A
unArg (arg _ x) = x

getArgInfo : Arg A → ArgInfo
getArgInfo (arg i _) = i

getVisibility : Arg A → Visibility
getVisibility = visibility ∘ getArgInfo

getRelevance : Arg A → Relevance
getRelevance = relevance ∘ getArgInfo

unAbs : Abs A → A
unAbs (abs _ x) = x

isVisible : Arg A → Bool
isVisible (arg (argInfo visible _) _) = true
isVisible _ = false

give : Term → Term → TC _
give = unify

quoteTC! : A → TC Term
quoteTC! a = quoteTC a >>= reduce

newMeta : Type → TC Term
newMeta = checkType unknown

isMeta : A → TC Bool
isMeta a = caseM quoteTC a of λ where
    (meta x []) → return true
    _           → return false

newMeta! : TC Term
newMeta! = newMeta unknown

`lam : Term → Term
`lam b = lam visible (abs "_" b)

infixl 9 _`∘_
_`∘_ : Term → Term → Term
_`∘_ = def₂ (quote _∘_)

infixr -20 _`$_
_`$_ : Term → Term → Term
_`$_ = def₂ (quote _$_)

infixr -10 _`$$_
_`$$_ : Term → Terms → Term
t `$$ [] = t
t `$$ (x ∷ args) = (t `$ x) `$$ args

infix 2 _=′_
_=′_ : Term → Term → TC ⊤
x =′ y = do -- unify x y
  debugPrint "mtac" 50 $ strErr "Unifying " ∷ termErr x ∷ strErr " with " ∷ termErr y ∷ []
  unify x y <|> (debugPrint "mtac" 50 (strErr "Failed" ∷ []) >> empty)
  debugPrint "mtac" 50 $ strErr "Succeed!" ∷ []

evalTC : TC A → Term → TC _
evalTC {A = A} c hole = do
  v  ← c
  `v ← quoteTC v
  `A ← quoteTC A
  checkedHole ← checkType hole `A
  unify checkedHole `v

macro
  runT : (Term → TC _) → Term → TC _
  runT t = t

  evalT : TC A → Term → TC _
  evalT = evalTC

define : Arg Name → Type → List Clause → TC ⊤
define f a cs = declareDef f a >> defineFun (unArg f) cs

typeErrorS : String → TC A
typeErrorS s = typeError (strErr s ∷ [])

blockOnMeta! : Meta → TC A
blockOnMeta! x = TC.bindTC commitTC λ _ → blockOnMeta x

inferNormalisedType : Term → TC Type
inferNormalisedType t = withNormalisation true (inferType t)

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

