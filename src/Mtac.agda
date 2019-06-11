{-# OPTIONS --without-K #-}

module Mtac where

open import Mtac.Core       public
  hiding (Tac; term; failed; error; return○′; return○; unquoteBind; bind○; runTT)
open import Mtac.Operations public
open import Mtac.Syntax     public
