open import Agda.Builtin.Reflection using (Term; TC; reduce; meta; unify
  ; getContext; var; catchTC; typeError; getInstances; inferType; strErr
  ; termErr)
  renaming (returnTC to return ; bindTC to _>>=_)
open import Data.Unit using (⊤)
open import Function.Base using (case_of_)
open import Data.List using (List; map; []; _∷_; downFrom; length)


module Utils where

inst : ∀ {A : Set} → ⦃ A ⦄ → A
inst ⦃ d ⦄ = d

private
  _>>_ : ∀ {ℓ} {A B : Set ℓ} → TC A → TC B → TC B
  x >> y = x >>= λ _ → y 

  oneOf : ∀ {ℓ} {A : Set ℓ} → List (TC A) → TC A
  oneOf [] = typeError []
  oneOf (a ∷ as) = catchTC a (oneOf as)

-- From: 
-- https://github.com/jespercockx/agda-core/blob/main/src/Utils/Tactics.agda
auto : Term → TC ⊤
auto hole = do
  hole ← reduce hole
  case hole of λ where
    (meta m _) → do
      let trySolution v = do
            -- debugPrint "auto" 10 (strErr "auto trying " ∷ termErr v ∷ [])
            unify hole v
      -- let debugSolutions vs = do
      --       `vs ← quoteTC vs
            -- debugPrint "auto" 10 (strErr "auto trying list " ∷ termErr `vs ∷ [])
      ctx ← getContext
      let vars = map (λ n → var n []) (downFrom (length ctx))
      -- debugSolutions vars
      catchTC (oneOf (map trySolution vars)) do
        -- debugPrint "auto" 10 (strErr "auto getting instances" ∷ [])
        cs ← getInstances m
        -- debugSolutions cs
        catchTC (oneOf (map trySolution cs)) do
          goal ← inferType hole
          typeError (strErr "auto could not find a value of type " ∷ termErr goal ∷ [])
    _ → typeError (strErr "auto called on already solved hole " ∷ termErr hole ∷ [])

-- Fills an implicit argument from the context
⦅_⦆ : ∀ {A B : Set} → (⦃ A ⦄ → B) → {@(tactic auto) _ : A} → B
⦅_⦆ x {y} = x ⦃ y ⦄

macro
  ?? : Term → TC ⊤
  ?? = auto