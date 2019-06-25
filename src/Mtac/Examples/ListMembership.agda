{-# OPTIONS --without-K  #-}

module Mtac.Examples.ListMembership where

open import Prelude
open import Mtac

infixr 5 _∈_
data _∈_ {A : Set ℓ} (x : A) : List A → Set ℓ where
  here  : ∀ {xs} →            x ∈ x ∷ xs
  there : ∀ {y xs} → x ∈ xs → x ∈ y ∷ xs

{-# TERMINATING #-}
search : (x : A) (xs : List A) → ○ (x ∈ xs)
search x xs = mcase xs ∶ (λ xs → x ∈ xs) of
  ∣ ys ∶ _ , x ∷ ys          ⇒  ⦇ here ⦈
  ∣ ys ∶ _ , y ∶ _ , y ∷ ys  ⇒  ⦇ there (search _ _) ⦈
  ∣ []                       ⇒  ⦇⦈
  end

4∈xs : 4 ∈ 1 ∷ 2 ∷ 3 ∷ 4 ∷ []
4∈xs =  run (search _ _)

∈-++ˡ : {A : Set ℓ} {x : A} {xs ys : List A} → x ∈ xs → x ∈ xs L.++ ys
∈-++ˡ here         = here
∈-++ˡ (there x∈xs) = there $ ∈-++ˡ x∈xs

∈-++ʳ : {A : Set ℓ} {x : A} (xs : List A) {ys : List A} → x ∈ ys → x ∈ xs L.++ ys
∈-++ʳ []       x∈ys = x∈ys
∈-++ʳ (x ∷ xs) x∈ys = there (∈-++ʳ xs x∈ys)

{-# TERMINATING #-}
search2 : {A : Set} (x : A) (xs : List A) → ○ (x ∈ xs)
search2 {A = A} x xs = mcase xs of
  ∣ xs ∶ _ , ys ∶ _ , xs ++ ys ⇒
    ⦇ ∈-++ˡ (search2 _ xs) | (∈-++ʳ xs) (search2 x ys) ⦈
  ∣ ys ∶ _ , x ∷ ys            ⇒ ⦇ here ⦈
  ∣ ys ∶ _ , y ∶ A , y ∷ ys    ⇒ ⦇ there (search2 _ _) ⦈
  ∣ []                        ⇒ ⦇⦈
  end

4∈xs++ys : 4 ∈ (3 ∷ 4 ∷ []) ++ (4 ∷ 5 ∷ [])
4∈xs++ys = run (search _ _)
