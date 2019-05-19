module Mtac.Operation where

open import Prelude 
open import Reflection.Extended hiding (getContext)

open import Mtac.Core

isEvar : {A : Set ℓ} → A → ○ Bool
isEvar {A} a = ◎ do
  (meta _ _) ← quoteTC a where _ → inj₂ <$> quoteTC false
  ⦇ inj₂ (quoteTC true) ⦈

getContext : ○ (Args Type)
getContext = fromTC TC.getContext

mdebugPrint : ℕ → ErrorParts → ○ ⊤
mdebugPrint n = fromTC ∘ print n

mprint : String → ○ ⊤
mprint str = mdebugPrint 2 [ strErr str ]
