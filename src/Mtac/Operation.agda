module Mtac.Operation where

open import Prelude 
open import Reflection.Extended hiding (getContext)

open import Mtac.Core

getContext : ○ Args Type
getContext = fromTC TC.getContext

mdebugPrint : ℕ → ErrorParts → ○ ⊤
mdebugPrint n = fromTC ∘ print n

mprint : ErrorParts → ○ ⊤
mprint errs = mdebugPrint 2 errs

`_` : A → ○ A
`_` = returnR

isEvar : {A : Set ℓ} → A → ○ Bool
isEvar {A} a = ◎ do
  (meta _ _) ← quoteTC a where _ → inj₂ <$> quoteTC false
  ⦇ inj₂ (quoteTC true) ⦈
