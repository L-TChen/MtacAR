{-# OPTIONS --type-in-type --without-K #-}

module Mtac.Pattern where

open import Prelude

open import Reflection.Extended
open import Mtac.Core 

data Patt {A : Set} (P : A → Set) : Set where
  Pbase : (x : A)   (px : ○ P x)     → Patt P
  Ptele : (C : Set) (f : C → Patt P) → Patt P

Patts : (P : A → Set) → ℕ → Set
Patts P n = Vec (Patt P) (suc n)

-- 
split : Term → TC (Term × Term)
splitGo : DiffList Term → (Term → Term) → Term → TC (Term × Term)

split  `pat = splitGo empty id `pat
splitGo metaCxt conVars (con (quote Ptele) (_ ∷ _ ∷ vArg `C   ∷ vArg (vLam s t) ∷ [])) = do
  x ← newMeta `C
  splitGo (metaCxt ++ [ x ]) (conVars ∘ vLam s) t
splitGo metaCxt conVars (con (quote Pbase) (_ ∷ _ ∷ vArg `lhs ∷ vArg `rhs ∷ [])) = do
  let metas = toList $ -, metaCxt
      `mlhs = conVars `lhs `$$ metas
      `mrhs = conVars `rhs `$$ metas
  return (`mlhs , `mrhs)
splitGo _ _ t = print 50 (strErr "Invalid pattern" ∷ termErr t ∷ []) >> azero
  
mmatch : (P : ∀ A → Set) (a : A) → Patts P n → ○ P a
mmatch P a patts =
  (joinR $ asum (map mmatchOne patts) >>= unquoteTC) <|> throw NoPatternMatched
  where
    mmatchOne : Patt P → TC Term
    mmatchOne pat = do 
      `a   ← quoteTC a
      `pat ← quoteTC pat
      `lhs , `rhs ← split `pat
      `lhs =′ `a
      return `rhs
