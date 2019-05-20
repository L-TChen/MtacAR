{-# OPTIONS --without-K --safe #-}

module Mtac.Core.Exception where

open import Prelude.Core

data Exception : Set where
  NotFound InvalidPattern EmptyClause NoPatternMatched NotImplemented : Exception

instance
  ExceptShow : Show Exception
  show ⦃ ExceptShow ⦄ NotFound         = "Not Found"
  show ⦃ ExceptShow ⦄ InvalidPattern   = "Invalid Pattern"
  show ⦃ ExceptShow ⦄ EmptyClause      = "Empty Clause"
  show ⦃ ExceptShow ⦄ NoPatternMatched = "No Pattern Matched"
  show ⦃ ExceptShow ⦄ NotImplemented   = "Not Implemented"
