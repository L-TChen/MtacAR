{-# OPTIONS --rewriting #-}

module Mtac.Core.Rewrite where

open import Agda.Builtin.Equality.Rewrite
open import Mtac.Core

{-# REWRITE identityTCˡ identityTCʳ #-}
{-# REWRITE quote-unquote #-}
{-# REWRITE ○-identityˡ #-}
