module Mtac.Operation where

open import Prelude 
open import Reflection.Extended hiding (getContext)

open import Mtac.Core

getContext : ○ Args Type
getContext = liftTC TC.getContext

mdebugPrint : ℕ → ErrorParts → ○ ⊤
mdebugPrint n = liftTC ∘ print n

mprint : ErrorParts → ○ ⊤
mprint errs = mdebugPrint 2 errs

`_` : A → ○ A
`_` = returnR

isEvar : {A : Set ℓ} → A → ○ Bool
isEvar {A} a = ◎ do
  (meta _ _) ← quoteTC a where _ → term <$> quoteTC false
  ⦇ term (quoteTC true) ⦈
