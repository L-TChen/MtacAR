{-# OPTIONS --without-K --safe #-}

module Mtac.Core.Exception where

open import Prelude.Core
open import Reflection.Extended

data Exception : Set where
  NoPatternMatched NotImplemented : Exception
  OutOfBound       : Term → Exception 
  NotVariable      : Term → Exception
  VariableNotFresh : Term → Exception 
  LocalName        : Exception
  NoMeta           : Type → Exception

toErrorPart : Exception → ErrorParts
toErrorPart NoPatternMatched = strErr "No pattern matched" ∷ []
toErrorPart NotImplemented   = strErr "Not implemented" ∷ []
toErrorPart (NotVariable `x) = strErr "Not a variable" ∷ termErr `x ∷ []
toErrorPart (OutOfBound `x)  = strErr "Out of bound" ∷ termErr `x ∷ [] 
toErrorPart LocalName        = strErr "The result contains a local name" ∷ []
toErrorPart (VariableNotFresh `x) = strErr "Some variable in the context depends on" ∷ termErr `x ∷ []
toErrorPart (NoMeta `A)      = strErr "Failed to create a metavariable for" ∷ termErr `A ∷ []
