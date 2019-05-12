module Reflection.Tactic.Eliminator where

open import Prelude

open import Reflection.Base
open import Reflection.DeBruijn

--------------------------------------------------------------------------------
-- Generate the type of elimination rule of a data type
-- For example 
--
-- data Vec {a : Level} (A : Set a) : ℕ → Set a where
--  []  : Vec {a} A zero
--  _∷_ : ∀ {n} (x : A) (xs : Vec {a} A n) → Vec {a} A (suc n)
--   
-- open import Data.Vec
-- elimVec : ∀ {a : Level} (A : Set a) {ℓ} {P : (n : ℕ) (v : Vec A n) → Set ℓ}
--   → P 0 []
--   → (∀ {n} (x : A) (xs : Vec A n) (Pxs : P n xs) → P (suc n) (x ∷ xs))
--   → (n : ℕ) → (xs : Vec A n) → P n xs
-- elimVec {a} A {ℓ} P[] Pcons 0       []       = P[]
-- elimVec {a} A {ℓ} P[] Pcons (suc n) (_∷_ {n} x xs) = Pcons x xs (elimVec {a} A {ℓ} P[] Pcons _ xs)

Args′ : Set → Set
Args′ A = DiffList (Arg A)

module _ where
  shiftArgs₀ : ℕ → Args′ Term → Args′ Term 
  shiftArgs₀ n = map (shiftArg n)

  takeArgs : ℕ → Type → ℕ → (Type → ℕ → Args′ Term → Type) → Type
  takeArgs n ty pos g = go n ty pos DiffList.[] g
    where
      go : ℕ → Type → ℕ → Args′ Term → (Type → ℕ → Args′ Term → Type) → Type
      go (ℕ.suc n) (Π[ s ∶ a@(arg i x) ] b) (ℕ.suc pos) args g =
        Π[ s ∶ a ] go n b pos (args ++ [ arg i (var₀ pos) ]) g
      go _       ty pos args g = g ty pos args

  takeAllArgs : ℕ → Type → (Type → Args′ Term → Type) → Type
  takeAllArgs pos ty g = takeArgs pos ty pos (λ ty _ args → g ty args)

  takeAllArgs′ = λ ty g → takeAllArgs (arity ty) ty g

  mkElimType : Name → Type → Names → ℕ → Type
  mkElimType dataId dataTy cs pars = 
    takeArgs pars dataTy (arity dataTy) (λ ty ar parArgs →
    hΠ[ "ℓ" ∶ def₀ (quote Level) ] 
    hΠ[ "P" ∶ takeAllArgs ar ty (λ _ args →
      vΠ[ "_" ∶ def dataId (toList (shiftArgs₀ 1 parArgs ++ args)) ] sortSet (var₀ (1 + ar))) ]
    takeAllArgs ar ty (λ _ args →
    -- insert inductive cases here
      vΠ[ "_" ∶ def dataId (toList (map (shiftArg 1) parArgs ++ args)) ]
      var (1 + ar) (toList ((map (shiftArg 1) args) ++ [ vArg (var₀ 0) ])))) -- should shift `parArgs` by # of cs 
    where
      mkCaseP : Name → Args′ Term → Type
      mkCaseP conId = {!!}

macro
  getInfo : Name → Term → TC ⊤ -- TC (Name × Type × ℕ × Names)
  getInfo id hole = do
    data-type pars cs ← getDefinition id
      where _ → typeError [ strErr "Not a data type" ]
    ty  ← getType id
    conTys ← sequence (map getType cs)
    typeError [ termErr (mkElimType id ty cs pars) ]

-- mkElimDef : Name → TC Clauses
-- mkElimDef = {!!}

-- mkElim : Name → Name → TC ⊤
-- mkElim id tyId = do
--   elimTy  ← {!!} -- mkElimType tyId
--   elimDef ← mkElimDef tyId
--   declareDef (vArg id) elimTy
--   defineFun id elimDef

-- ℕT : Term
-- ℕT = Π[ "ℓ" ∶ hArg (def (quote Level) []) ]
--   hΠ[ "P" ∶ vΠ[ "_" ∶ def (quote ℕ) [] ] sortSet (var 1 []) ]
--   vΠ[ "Pz" ∶ var 0 [ vArg (con (quote ℕ.zero) []) ] ]
--   vΠ[ "Ps" ∶ vΠ[ "n" ∶ def (quote ℕ) [] ] vΠ[ "_" ∶ var 2 [ vArg (var₀ 0) ] ] var 3 [ vArg (con (quote ℕ.suc) [ vArg (var₀ 1) ]) ] ]
--   vΠ[ "n" ∶ def (quote ℕ) [] ] var 3 [ vArg (var₀ 0) ]

-- mkElimℕ : Name → TC ⊤
-- mkElimℕ id = do
--   ty ← quoteTC ℕ
--   declareDef (vArg id) ℕT
--   defineFun id
--     ( (vArg (var "P0") ∷ vArg (var "Psuc") ∷ vArg (con (quote ℕ.zero) []) ∷ []) ↦ var₀ 1
--     ∷ (vArg (var "P0") ∷ vArg (var "Psuc") ∷ vArg (con (quote ℕ.suc) [ vArg (var "n") ]) ∷ []) 
--       var 1 (vArg (var₀ 0) ∷ vArg (def id (vArg (var₀ 2) ∷ vArg (var₀ 1) ∷ vArg (var₀ 0) ∷ [])) ∷ [])
--     ∷ [])
-- unquoteDecl elimℕ′ = mklimℕ elimℕ′ 
