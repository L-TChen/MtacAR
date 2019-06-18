{-# OPTIONS --omega-in-omega #-}

module Mtac2.Core.Base where

open import Prelude
open import Reflection.Extended hiding (Cxt)

open import Mtac

data Goal {ℓ : Level} : Set (lsuc ℓ) where
  GBase : {A : Set ℓ} (x : A) → Goal
  GTele : (B : Set ℓ) (Q : B → Goal {ℓ}) → Goal

Goals : Set (lsuc ℓ)
Goals {ℓ} = List (Goal {ℓ})

Tactic : Set (lsuc ℓ)
Tactic {ℓ} = Goal {ℓ} → ○ (Goals {ℓ})

isUnsolved : Goal {ℓ} → TC Bool
isUnsolved (GBase x) = isMeta x
isUnsolved (GTele A P) = quoteTC A >>= λ `A → extendContext (vArg `A) do
  a ← unquoteTC {A = A} (var₀ 0)
  isUnsolved (P a)

filterSolved : Goals {ℓ} → TC Goals
filterSolved = filterA isUnsolved

closeGoals : {A : Set ℓ} (x : A) → Goals {ℓ} → ○ Goals {ℓ}
closeGoals x = traverse λ g → GTele _ <$> (ƛ x ⇒ ⦇ g ⦈)

openApply : Tactic {ℓ} → Goal → ○ Goals
openApply tac g@(GBase x) = tac g
openApply tac (GTele B P) = ν x ∶ B ⇒
  openApply tac (P x) >>= closeGoals x

tacBind : (t u : Tactic {ℓ}) → Tactic {ℓ}
tacBind t u g = do
  gs ← liftTC ∘ filterSolved =<< t g
  concat <$> traverse {T = List} (openApply u) gs


exact : {A : Set ℓ} → A → Goal {ℓ} → ○ Goal {ℓ}
exact {A = A} a (GBase {B} x) = mcase B of
  ∣ A ⇒ ⦇ (GBase x) ⦈
  ∣ B ⇒ ⦇⦈
  end
exact {A = A} a (GTele B Q) = ⦇⦈

cintro : {A : Set ℓ} (t : A → Tactic {ℓ}) → Tactic {ℓ}
cintro {ℓ} {A} t g = mcase g of
  ∣ P ∶ (A → Set ℓ) , e ∶ (∀ x → P x) , GBase e ⇒ (do
    ν x ∶ A ⇒ (do
      Px ← liftTC $ unquoteTC {A = Set ℓ} =<< quoteTC! (P x)
      e′ ← mvar Px
      nG ← ƛ x ⇒ return e′
      exact nG g
      closeGoals x =<< t x (GBase e)))
  ∣ B ∶ Set ℓ , e ∶ B , GBase e  ⇒ ⦇⦈
  ∣ g ⇒ ⦇⦈
  end

runM2 : Tactic {ℓ} → Term → TC ⊤
runM2 = {!!}

lem : Tactic {ℓ}
lem = {!cintro ?!}
