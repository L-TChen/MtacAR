module Reflection.Base where

open import Prelude

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

Script = Term → TC ⊤

macro
  showCons : Name → Script
  showCons id hole = do
    data-type pars cs ← getDefinition id
      where _ → typeError [ strErr "Not a data type" ]
    typeError (map nameErr cs)

  fill : Term → Script
  fill = unify

arity : Term → ℕ
arity (Π[ _ ∶ _ ] b) = 1 + arity b
arity _              = 0

{-
private
  variable
    n : ℕ
mutual
  data Even : ℕ → Set where
    z   : Even 0
    ss  : Odd n → Even (succ n)
  data Odd : ℕ → Set where
    one : Even n → Odd (succ n)

module _ {P : ∀ n → Even n → Set} {Q : ∀ n → Odd n → Set}
  (Pz : P 0 z)(Pss : ∀ n o → Q n o → P (succ n) (ss o)) (Pone : ∀ n e → P n e → Q (succ n) (one e)) where
  mutual
    elimEven : ∀ n → (e : Even n) → P n e
    elimEven .0 z = Pz
    elimEven .(succ _) (ss x) = Pss _ x  (elimOdd _ x)

    elimOdd  : ∀ n → (o : Odd n) → Q n o
    elimOdd .(succ _) (one x) = Pone _ x (elimEven _ x)

elimEven′ : {P : ∀ n → Even n → Set}
  → (Pz : P 0 z) → (Pss : ∀ n → (o : Odd n) → P (succ n) (ss o))
  → ∀ n → (e : Even n) → P n e
elimEven′ Pz Pss .0 z = Pz
elimEven′ Pz Pss .(succ (succ _)) (ss (one x)) = Pss _ ((one x))
-}
