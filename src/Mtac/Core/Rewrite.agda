{-# OPTIONS --rewriting #-}

module Mtac.Core.Rewrite where

open import Agda.Builtin.Equality.Rewrite
open import Mtac.Core.MonadLaw

{-# REWRITE identityTCˡ identityTCʳ #-}
{-# REWRITE quote-unquote #-}
{-# REWRITE ○-identityˡ #-}
