{-# OPTIONS --type-in-type #-}

open import Data.Empty using (⊥; ⊥-elim)
open import Function.Base using (_$_; _∘_; const)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst)
open import Relation.Nullary.Negation using (¬_; contradiction)
open import Data.Unit using (⊤; tt)

open import IntrinFinMap using (FinMap)
  renaming (insert to insert-map; merge to merge-map
  ; insert-com to insert-com-map)
open import Ord using (Ord)

module IntrinFinSet where

FinSet : (A : Set) ⦃ _ : Ord A ⦄ → Set
FinSet A = FinMap A ⊤

insert : ∀ {A : Set} ⦃ _ : Ord A ⦄ → A → FinSet A → FinSet A
insert x s = insert-map x tt s

merge : ∀ {A : Set} ⦃ _ : Ord A ⦄ → FinSet A → FinSet A → FinSet A
merge = merge-map

insert-com : ∀ {A : Set} ⦃ _ : Ord A ⦄ (x y : A) (zs : FinSet A)
           → insert x (insert y zs) ≡ insert y (insert x zs)
insert-com x y s = insert-com-map x y tt tt s $ const refl
