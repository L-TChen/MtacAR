------------------------------------------------------------------------
-- Encode a context as a list of types using type in type 
{-# OPTIONS --type-in-type #-} 
module Mtac.Context where

open import Prelude 
open import Reflection.Extended

open import Mtac.Core

data Dyn : Set where
  dyn : (A : Set) → A → Dyn

{-
{-# TERMINATING #-}
pick : (A : Set) → List Dyn → ○ A
pick A xs =
  mcase xs of
    ∣ x :> ys :> (dyn A x) ∷ ys ⇒ return x
    ∣ d :> ys :> d ∷ ys         ⇒ pick A ys
    ∣ []                        ⇒ throw NotFound
  end
-}
