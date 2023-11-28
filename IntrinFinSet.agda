{-# OPTIONS --type-in-type #-}

open import Data.Empty using (⊥; ⊥-elim)
open import Function.Base using (_$_; _∘_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst)
open import Relation.Nullary.Negation using (¬_; contradiction)

open import Utils using (inst; ??; ⦅_⦆)

-- A finite set modelled off a correct-by-construction ordered list, inspired
-- by Connor's "How to Keep Your Neighbours in Order"
module IntrinFinSet where

infixr 5 _∷_

data CMP {A : Set} (R : A → A → Set) : A → A → Set where
  LT : ∀ {x y} → ⦃ R x y ⦄ → CMP R x y
  GT : ∀ {x y} → ⦃ R y x ⦄ → CMP R x y
  EQ : ∀ {x}              → CMP R x x 

record Ord (A : Set) : Set

_>_ : ∀ {A : Set} → ⦃ Ord A ⦄ → A → A → Set

record Ord A where
  field
    _<_      : A → A → Set
    compare  : ∀ x y → CMP _<_ x y
    <trans   : ∀ {x y z} → x < y → y < z → x < z
    <irref   : ∀ {x y} → x < y → ¬ y < x
    <antisym : ∀ {x y} → x < y → ¬ x ≡ y
    -- Uniqueness-of-Less-Than-Proofs
    uo<p     : ∀ {x y} (x<y₁ x<y₂ : x < y) → x<y₁ ≡ x<y₂

open Ord ⦃...⦄

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

-- Like Connor's `OList`, but we use a strict less-than relation `_<_` to ensure
-- there are no duplicates
data OFS {A : Set} ⦃ _ : Ord A ⦄ (l u : A +∞) : Set where
  []  :       ⦃ l <A+∞ u ⦄                       → OFS l u
  _∷_ : ∀ p → ⦃ l <A+∞ (inj p) ⦄ → OFS (inj p) u → OFS l u

pattern cons x xs p = _∷_ x ⦃ p ⦄ xs

insert : ∀ {A : Set} {l u : A +∞} ⦃ _ : Ord A ⦄ (x : A) 
       → ⦃ l <A+∞ inj x ⦄ → ⦃ inj x <A+∞ u ⦄ → OFS l u → OFS l u
insert x [] = x ∷ []
insert x (_∷_ y ⦃ y<l ⦄ ys) with compare (inj x) (inj y)
... | LT = x ∷ y ∷ ys
... | GT = y ∷ insert x ys
... | EQ = _∷_ y ⦃ y<l ⦄ ys

{-# TERMINATING #-}
merge : ∀ {A : Set} {l u : A +∞} ⦃ _ : Ord A ⦄ 
      → OFS l u → OFS l u → OFS l u
merge []   ys = ys
merge xs   [] = xs
merge (cons x xs l<x) (y ∷ ys) with compare (inj x) (inj y)
... | LT = x ∷ merge xs (y ∷ ys)
... | GT = y ∷ merge (x ∷ xs) ys
... | EQ with ys
... | [] = cons x xs l<x
... | (y₁ ∷ ys₁) 
  = merge (cons x xs l<x) (cons y₁ ys₁ $ <trans ⦃ Ord-A+∞ ⦄ l<x inst)

insert-xy≡insert-yx : ∀ {A : Set} ⦃ _ : Ord A ⦄ {l u : A +∞} (x y : A)
                        ⦃ l<x : l <A+∞ inj x ⦄ ⦃ x<u : inj x <A+∞ u ⦄
                        ⦃ l<y : l <A+∞ inj y ⦄ ⦃ y<u : inj y <A+∞ u ⦄
                        (zs : OFS l u)
                    → insert x (insert y zs) ≡ insert y (insert x zs)
insert-xy≡insert-yx {A} x y [] with compare (inj x) (inj y)
... | GT ⦃ x>y ⦄ rewrite compare-coh< {A +∞} x>y = refl
... | LT ⦃ x<y ⦄ rewrite compare-coh> {A +∞} x<y = refl
insert-xy≡insert-yx {A} x x ⦃ l<x ⦄ ⦃ x<u ⦄ ⦃ l<y ⦄ ⦃ y<u ⦄ [] | EQ 
  rewrite compare-coh≡ {x = inj x} 
  rewrite uo<p {A +∞} x<u y<u
  rewrite uo<p {A +∞} l<x l<y = refl
insert-xy≡insert-yx {A} x y (z ∷ zs) with compare (inj x) (inj z) in cmp-xz
                                    | compare (inj y) (inj z) in cmp-yz
... | GT | GT rewrite cmp-xz rewrite cmp-yz 
  = cong (_∷_ z) $ insert-xy≡insert-yx x y zs
... | LT | LT with compare (inj x) (inj y)
... | GT ⦃ x>y ⦄ rewrite cmp-xz rewrite compare-coh< {A +∞} x>y = refl
... | LT ⦃ x<y ⦄ rewrite compare-coh> {A +∞} x<y rewrite cmp-yz = refl
insert-xy≡insert-yx {A} x x ⦃ l<x ⦄ ⦃ _ ⦄ ⦃ l<y ⦄ (z ∷ zs) 
  | LT ⦃ x<z ⦄ | LT ⦃ y<z ⦄ | EQ rewrite compare-coh≡ {x = inj x}
  rewrite uo<p {A +∞} x<z y<z rewrite uo<p {A +∞} l<x l<y = refl
insert-xy≡insert-yx {A} x y (z ∷ zs) | LT ⦃ x<z ⦄ | GT ⦃ y>z ⦄ 
  with compare (inj y) (inj x)
... | GT rewrite cmp-xz rewrite cmp-yz = refl
... | EQ = ⊥-elim $ <irref {A +∞} x<z y>z
... | LT = ⊥-elim $ <irref {A +∞} x<z $ <trans {A +∞} y>z inst
insert-xy≡insert-yx {A} x y (z ∷ zs) | GT ⦃ x>z ⦄ | LT ⦃ y<z ⦄ 
  with compare (inj x) (inj y)
... | GT rewrite cmp-xz rewrite cmp-yz  = refl
... | EQ = ⊥-elim $ <irref {A +∞} x>z y<z
... | LT = ⊥-elim $ <irref {A +∞} x>z $ <trans {A +∞} inst y<z
insert-xy≡insert-yx {A} x y (y ∷ zs) | GT ⦃ x>z ⦄ | EQ 
    with compare (inj x) (inj y)
... | GT ⦃ x>y ⦄ rewrite compare-coh≡ {x = inj y} rewrite uo<p {A +∞} x>z x>y
  = refl
... | LT ⦃ x<y ⦄ = ⊥-elim $ <irref {A +∞} x>z x<y
... | EQ = ⊥-elim $ <antisym {A +∞} x>z refl
insert-xy≡insert-yx {A} x y (x ∷ zs) | EQ | GT ⦃ y<z ⦄ 
    with compare (inj y) (inj x)
... | GT ⦃ x<y ⦄ rewrite compare-coh≡ {x = inj x} rewrite uo<p {A +∞} y<z x<y
  = refl
... | LT = ⊥-elim $ <irref {A +∞} y<z inst
... | EQ = ⊥-elim $ <antisym {A +∞} y<z refl
insert-xy≡insert-yx {A} x y (x ∷ zs) | EQ | LT ⦃ y<z ⦄ 
    with compare (inj x) (inj y)
... | GT ⦃ x>y ⦄ 
  rewrite compare-coh< {A +∞} x>y rewrite compare-coh≡ {x = inj x}
  rewrite uo<p {A +∞} y<z x>y = refl
... | LT = ⊥-elim $ <irref {A +∞} y<z inst
... | EQ = ⊥-elim $ <antisym {A +∞} y<z refl
insert-xy≡insert-yx {A} x y (y ∷ zs) | LT ⦃ x<z ⦄ | EQ 
    with compare (inj x) (inj y) in cmp-xy
... | LT ⦃ x<y ⦄ 
  rewrite compare-coh> {A +∞} x<z rewrite compare-coh≡ {x = inj y} 
  rewrite uo<p {A +∞} x<y x<z = refl
... | GT = ⊥-elim $ <irref {A +∞} x<z inst
... | EQ = ⊥-elim $ <antisym {A +∞} x<z refl
insert-xy≡insert-yx {A} x x ⦃ l<x ⦄ ⦃ x<u ⦄ ⦃ l<y ⦄ ⦃ y<u ⦄ (z ∷ zs) | EQ | EQ
  rewrite uo<p {A +∞} l<x l<y rewrite uo<p {A +∞} x<u y<u = refl

FinSet : (A : Set) ⦃ _ : Ord A ⦄ → Set
FinSet A = OFS {A} -∞ ∞
