{-# OPTIONS --allow-unsolved-metas #-} 

module Reflection.Base where

open import Prelude
open import Reflection.Recursion public

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

Script     = Term → TC ⊤
Types      = List Type
Terms      = List Term
ErrorParts = List ErrorPart

macro
  showCons : Name → Script
  showCons id hole = do
    data-type pars cs ← getDefinition id
      where _ → typeError [ strErr "Not a data type" ]
    typeError (map nameErr cs)

  fill : Term → Script
  fill = unify

  runTC : {A : Set ℓ} → TC A → Script
  runTC t _ = t >>=TC λ _ → return tt

arity : Term → ℕ
arity (Π[ _ ∶ _ ] b) = 1 + arity b
arity _              = 0

body : Arg Term → Term
body (arg i x) = x


infixl 10 _!!_
_!!_ : List A → ℕ → Maybe A
[]       !! _       = nothing
(x ∷ xs) !! zero    = just x
(x ∷ xs) !! (suc n) = xs !! n

varsToMetas : List Meta → Term → Term
varsToMetas metaCxt = recTerm metaOrVar
  con def lam pat-lam pi sort set lit unknown lit meta unknown clause absurd-clause
  where
    metaOrVar : ℕ → Args Term → Term
    metaOrVar n args with metaCxt !! n
    ... | nothing = var n args
    ... | just x  = meta x args
     
newMeta' : Type → TC Meta
newMeta' t = do
  meta m [] ← checkType unknown t
    where _ → typeError [ strErr "not a meta variable" ]
  return m
