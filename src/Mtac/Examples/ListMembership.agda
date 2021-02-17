{-# OPTIONS --without-K -v mtac:50  #-}

module Mtac.Examples.ListMembership where

open import Prelude
open import Mtac

infixr 5 _∈_

data _∈_ {A : Set} (x : A) : List A → Set where
  here  : {xs : List A}                  → x ∈ x ∷ xs
  there : {y : A} {xs : List A} → x ∈ xs → x ∈ y ∷ xs

{-# TERMINATING #-}
search : (x : A) (xs : List A) → ○ (x ∈ xs)
search x xs = mcase xs ∶ (λ xs → x ∈ xs) of
  ∣ ys ∶ _ , x ∷ ys          ⇒  ⦇ here ⦈
  ∣ ys ∶ _ , y ∶ _ , y ∷ ys  ⇒  ⦇ there (search x ys) ⦈
  ∣ []                       ⇒  ⦇⦈
  end

4∈xs : 2 ∈ (2 ∷ []) ++ 1 ∷ 2 ∷ 3 ∷ 4 ∷ []
4∈xs = run (search _ _)

-- ∈-++ˡ : {A : Set} {x : A} {xs : List A} (ys : List A) → x ∈ xs → x ∈ xs L.++ ys
-- ∈-++ˡ _ here         = here
-- ∈-++ˡ ys (there x∈xs) = there $ ∈-++ˡ ys x∈xs

-- ∈-++ʳ : {A : Set} {x : A} (xs : List A) {ys : List A} → x ∈ ys → x ∈ xs L.++ ys
-- ∈-++ʳ []       x∈ys = x∈ys
-- ∈-++ʳ (x ∷ xs) x∈ys = there (∈-++ʳ xs x∈ys)

open import Reflection.Extended
-- {-# TERMINATING #-}
-- search2 : {A : Set} (x : A) (xs : List A) → ○ (x ∈ xs)
-- search2 {A = A} x xs = mcase xs of
--   ∣ ys ∶ List A , zs ∶ List A , ys L.++ zs ⇒
--     ⦇ (∈-++ˡ zs) (search2 x ys) | (∈-++ʳ ys) (search2 x zs) ⦈
--   ∣ ys ∶ List A , x ∷ ys                   ⇒ ⦇ here ⦈
--   ∣ ys ∶ List A , y ∶ A , y ∷ ys           ⇒ ⦇ there (search2 x ys) ⦈
--   ∣ []                                     ⇒ ⦇⦈
--   end

-- 4∈xs++ys : (xs : List ℕ) → 3 ∈ L._++_ xs (3 ∷ 4 ∷ [])
-- 4∈xs++ys xs = run (search2 3 (xs L.++ (3 ∷ 4 ∷ [])))

f : Term → Term
f (quoteTerm 3) = {!!}
f t = ?
