module Tactic.Simple where

open import Tactic
open import Data.List

macro
  assumption : Term → Term → TC ⊤
  assumption t hole = do
    holeTy ← inferType hole
    cxt    ← getContext 
    {!!}
