{-# OPTIONS --without-K --safe #-}

module Mtac.Core.Exception where

open import Prelude.Core
open import Reflection.Extended

data Exception : Set where
  InvalidPattern EmptyClause NoPatternMatched NotImplemented : Exception
  NotFound : Exception 
  StuckTerm : Term → Exception

toErrorPart : Exception → ErrorParts 
toErrorPart NotFound         = strErr "Not Proof Found" ∷ []  
toErrorPart InvalidPattern   = strErr "Invalid Pattern" ∷ []
toErrorPart EmptyClause      = strErr "Empty Clause" ∷ []
toErrorPart NoPatternMatched = strErr "No Pattern Matched" ∷ []
toErrorPart NotImplemented   = strErr "Not Implemented" ∷ []
toErrorPart (StuckTerm `x)   = strErr "Computation stucked on" ∷ termErr `x ∷ []
