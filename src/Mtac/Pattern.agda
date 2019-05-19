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

split : Term → TC (Term × Term)
split `pat = go empty id `pat
  where
    go : DiffList Term → (Term → Term) → Term → TC (Term × Term)
    go metaCxt conVars (con (quote Pbase) (_ ∷ _ ∷ vArg `lhs ∷ vArg `rhs ∷ [])) = do
      let metas = toList $ _ , metaCxt
          `mlhs = (conVars `lhs) `$$ metas
          `mrhs = (conVars `rhs) `$$ metas
      return $ `mlhs , `mrhs
    go metaCxt conVars (con (quote Ptele) (_ ∷ _ ∷ vArg `C   ∷ vArg (vLam s t) ∷ [])) = do
      x ← newMeta `C
      go (metaCxt ++ [ x ]) (conVars ∘ (vLam s)) t
    go _ _ t = print 20 (strErr "Invalid pattern" ∷ termErr t ∷ []) >> azero
  
mmatch : (P : ∀ A → Set) (a : A) → Patts P n → ○ P a
mmatch P a patts =
  (joinR $ asum (map mmatchOne patts) >>= unquoteTC) <|> throw NoPatternMatched
  where
    mmatchOne : Patt P → TC Term
    mmatchOne pat = do
      `a   ← quoteTC a
      `pat ← quoteTC pat
      `lhs , `rhs ← split `pat
      print 10 $ strErr "LHS:" ∷ termErr `lhs ∷ strErr "\nRHS:" ∷ termErr `rhs ∷ []
      `lhs =′ `a
      `rhs ← reduce `rhs
      print 10 $ strErr "Reduced RHS:" ∷ termErr `rhs ∷ []
      return `rhs
      
{-
patt1 = quoteTerm (Pbase {P = λ (x : Set) → x } ⊤ (return tt))
patt2 = quoteTerm (Ptele {P = λ (x : Set) → x } Set λ x → Pbase ⊤ (return tt))
patt3 = Pbase {P = λ (x : Set) → x } ⊤ (return tt)
patt4 = Ptele {P = λ (x : Set) → x } Set λ x → Pbase ⊤ (return tt)
-}

