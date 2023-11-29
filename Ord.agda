{-# OPTIONS --type-in-type #-}

open import Relation.Nullary.Negation using (¬_)
open import Data.Empty using (⊥-elim) 
open import Data.Bool using (Bool; true; false)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Function.Base using (_$_)

open import Utils using (inst)

module Ord where

data CMP {A : Set} (R : A → A → Set) : A → A → Set where
  LT : ∀ {x y} → ⦃ R x y ⦄ → CMP R x y
  GT : ∀ {x y} → ⦃ R y x ⦄ → CMP R x y
  EQ : ∀ {x}               → CMP R x x 

record Ord (A : Set) : Set

_>_ : ∀ {A : Set} → ⦃ Ord A ⦄ → A → A → Set

record Ord A where
  field
    _<_      : A → A → Set
    compare  : ∀ x y → CMP _<_ x y
    <trans   : ∀ {x y z} → x < y → y < z → x < z
    <irref   : ∀ {x y}   → x < y → ¬ y < x
    <antisym : ∀ {x y}   → x < y → ¬ x ≡ y
    -- Uniqueness-of-Less-Than-Proofs
    uo<p     : ∀ {x y} (x<y₁ x<y₂ : x < y) → x<y₁ ≡ x<y₂

open Ord ⦃...⦄ public

x > y = y < x

compare-coh≡ : ∀ {A : Set} ⦃ _ : Ord A ⦄ {x : A} → compare x x ≡ EQ
compare-coh≡ {x = x} with compare x x
... | EQ = refl
... | LT ⦃ x<x ⦄ = ⊥-elim $ <antisym x<x refl
... | GT ⦃ x<x ⦄ = ⊥-elim $ <antisym x<x refl

compare-coh< : ∀ {A : Set} ⦃ _ : Ord A ⦄ {x y : A} (x<y : x < y) 
             → compare x y ≡ LT ⦃ x<y ⦄
compare-coh< ⦃ OrdA ⦄ {x} {y} x<y with compare x y
... | LT ⦃ x<y' ⦄ = cong (λ x → LT ⦃ x ⦄) $ uo<p ⦃ OrdA ⦄ x<y' x<y
... | GT ⦃ x>y  ⦄ = ⊥-elim $ <irref x<y x>y
... | EQ         = ⊥-elim $ <antisym x<y refl

compare-coh> : ∀ {A : Set} ⦃ _ : Ord A ⦄ {x y : A} 
                 (x>y : y < x) 
             → compare x y ≡ GT ⦃ x>y ⦄
compare-coh> ⦃ OrdA ⦄ {x} {y} x>y with compare x y
... | GT ⦃ x>y' ⦄ = cong (λ x → GT ⦃ x ⦄) $ uo<p ⦃ OrdA ⦄ x>y' x>y
... | LT ⦃ x<y  ⦄ = ⊥-elim $ <irref x>y x<y
... | EQ         = ⊥-elim $ <antisym x>y refl

Cmp : ∀ {A : Set} → ⦃ Ord A ⦄ → A → A → Set
Cmp = CMP _<_

-- A datatype extended with -∞ and ∞
data _+∞ (A : Set) : Set where
  ∞   : A +∞
  inj : A → A +∞
  -∞  : A +∞ 

data _<A+∞_ {A : Set} ⦃ _ : Ord A ⦄ : A +∞ → A +∞ → Set where
  lift : ∀ {x y} → x < y → inj x <A+∞ inj y   
  instance 
    x<∞  : ∀ {x} → inj x <A+∞ ∞
    -∞<y : ∀ {y} →    -∞ <A+∞ inj y
    -∞<∞ :            -∞ <A+∞ ∞   

instance 
  Ord-A+∞ : ∀ {A : Set} → ⦃ Ord A ⦄ → Ord $ A +∞
  _<_      ⦃ Ord-A+∞ ⦄     = _<A+∞_
  compare  ⦃ Ord-A+∞ ⦄ (inj _)  ∞ = LT
  compare  ⦃ Ord-A+∞ ⦄ (inj _) -∞ = GT
  compare  ⦃ Ord-A+∞ ⦄ -∞ (inj _) = LT
  compare  ⦃ Ord-A+∞ ⦄  ∞ (inj _) = GT
  compare  ⦃ Ord-A+∞ ⦄ -∞       ∞ = LT
  compare  ⦃ Ord-A+∞ ⦄  ∞      -∞ = GT
  compare  ⦃ Ord-A+∞ ⦄  ∞       ∞ = EQ
  compare  ⦃ Ord-A+∞ ⦄ -∞      -∞ = EQ
  compare  ⦃ Ord-A+∞ ⦄ (inj x) (inj y) with compare x y
  ... | LT = LT ⦃ lift inst ⦄
  ... | GT = GT ⦃ lift inst ⦄
  ... | EQ = EQ
  <trans   ⦃ Ord-A+∞ ⦄ -∞<y     x<∞          = -∞<∞
  <trans   ⦃ Ord-A+∞ ⦄ (lift x<y) x<∞        =  x<∞
  <trans   ⦃ Ord-A+∞ ⦄ -∞<y     (lift _)     = -∞<y    
  <trans   ⦃ Ord-A+∞ {A} ⦄ (lift x<y) (lift y<z) = lift $ <trans {A} x<y y<z
  <irref   ⦃ Ord-A+∞ {A} ⦄ (lift x<y) (lift y<x) = <irref {A} x<y y<x
  <antisym ⦃ Ord-A+∞ {A} ⦄ (lift x<y) refl = <antisym {A} x<y refl
  uo<p     ⦃ Ord-A+∞ ⦄ -∞<∞ -∞<∞ = refl
  uo<p     ⦃ Ord-A+∞ ⦄  x<∞  x<∞ = refl
  uo<p     ⦃ Ord-A+∞ ⦄ -∞<y -∞<y = refl
  uo<p     ⦃ Ord-A+∞ {A} ⦄ (lift p₁) (lift p₂) = cong lift $ uo<p {A} p₁ p₂

_==_ : ∀ {A : Set} → ⦃ Ord A ⦄ → A → A → Bool
x == y with compare x y
... | EQ = true
... | GT = false
... | LT = false
