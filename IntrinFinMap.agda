{-# OPTIONS --type-in-type #-}

open import Data.Empty using (⊥; ⊥-elim)
open import Function.Base using (_$_; _∘_)
open import Relation.Binary.PropositionalEquality 
  using (_≡_; refl; cong; subst; sym)
open import Relation.Nullary.Negation using (¬_; contradiction)
open import Data.Sum using (_⊎_; inj₁; inj₂)

open import Ord 
  using (Ord; _<_; compare; <trans; <irref; <antisym; uo<p; _>_; compare-coh≡
  ; compare-coh<; compare-coh>; Cmp; LT; GT; EQ; _+∞; ∞; -∞; _<A+∞_; inj; -∞<y
  ; x<∞; -∞<∞)
open import Utils using (inst)

-- A finite map modelled off a correct-by-construction ordered list, inspired
-- by Connor's "How to Keep Your Neighbours in Order"
module IntrinFinMap where

infixr 5 _↦_∷_
infix 4 _↦_∈_

-- Like Connor's `OList`, but we use a strict less-than relation `_<_` to ensure
-- there are no duplicates, and carry around an associated value with each 
-- element
data OFM {K : Set} ⦃ _ : Ord K ⦄ (V : Set) (l u : K +∞) : Set where
  []  :       ⦃ l <A+∞ u ⦄                       → OFM V l u
  _↦_∷_ : ∀ p → V → OFM V (inj p) u → ⦃ l <A+∞ (inj p) ⦄ → OFM V l u

pattern cons k v kvs p = _↦_∷_ k v kvs ⦃ p ⦄

insert : ∀ {K V : Set} {l u : K +∞} ⦃ _ : Ord K ⦄ (x : K) → V 
       → ⦃ l <A+∞ inj x ⦄ → ⦃ inj x <A+∞ u ⦄ → OFM V l u → OFM V l u
insert k  v  [] = k ↦ v ∷ []
insert k₁ v₁ m@(k₂ ↦ v₂ ∷ kvs) with compare (inj k₁) (inj k₂)
... | LT = k₁ ↦ v₁ ∷ k₂ ↦ v₂ ∷ kvs
... | GT = k₂ ↦ v₂ ∷ insert k₁ v₁ kvs
... | EQ = m

{-# TERMINATING #-}
merge : ∀ {K V : Set} {l u : K +∞} ⦃ _ : Ord K ⦄ 
      → OFM V l u → OFM V l u → OFM V l u
merge []   ys = ys
merge xs   [] = xs
merge {K} m₁@(cons k₁ v₁ kvs₁ l<k₁) (k₂ ↦ v₂ ∷ kvs₂) 
    with compare (inj k₁) (inj k₂)
... | LT = k₁ ↦ v₁ ∷ merge kvs₁ (k₂ ↦ v₂ ∷ kvs₂)
... | GT = k₂ ↦ v₂ ∷ merge (k₁ ↦ v₁ ∷ kvs₁) kvs₂
... | EQ with kvs₂
... | [] = m₁
... | k₃ ↦ v₃ ∷ kvs₃ 
  = merge (cons k₁ v₁ kvs₁ l<k₁) (cons k₃ v₃ kvs₃ $ <trans {K +∞} l<k₁ inst)

data _↦_∈_ {K V : Set} ⦃ _ : Ord K ⦄ {l u : K +∞} : K → V → OFM V l u 
                                                  → Set where
  here  : ∀ {k v kvs} ⦃ _ : l < inj k ⦄ 
        → k ↦ v ∈ k  ↦ v  ∷ kvs
  there : ∀ {k₁ v₁ k₂ v₂ kvs} ⦃ _ : l < inj k₁ ⦄ 
        → k₂ ↦ v₂ ∈ kvs → k₂ ↦ v₂ ∈ k₁ ↦ v₁ ∷ kvs


module _ {K V : Set} ⦃ _ : Ord K ⦄ where

  record _∈_ {l u : K +∞} (k : K) (kvs : OFM V l u) : Set where
    constructor ⟨_⟩
    field
      {v}  : V
      ev : k ↦ v ∈ kvs

  infix 4 _∈_
  infix 4 _∉_
  
  _∉_ : ∀ {l u : K +∞} → K → OFM V l u → Set
  k ∉ kvs = ¬ k ∈ kvs

  k<l→k∉kvs : ∀ {l u : K +∞} (k : K) (kvs : OFM V l u) → ⦃ inj k < l ⦄ → k ∉ kvs
  k<l→k∉kvs k  (cons k  v₂ kvs l<k)           ⟨ here ⟩ = <irref {K +∞} l<k inst
  k<l→k∉kvs k₁ (cons k₂ v₂ kvs l<k₂) ⦃ k₁<l ⦄ ⟨ there k₁∈kvs ⟩ 
    = k<l→k∉kvs k₁ kvs ⦃ <trans {K +∞} k₁<l l<k₂ ⦄ ⟨ k₁∈kvs ⟩

  _∈?_ : ∀ {l u : K +∞} (k : K) (kvs : OFM V l u) → k ∈ kvs ⊎ k ∉ kvs 
  k  ∈? [] = inj₂ $ λ ()
  k₁ ∈? (k₂ ↦ v₂ ∷ kvs) with compare (inj k₁) (inj k₂)
  ... | EQ = inj₁ ⟨ here ⟩
  ... | LT ⦃ k₁<k₂ ⦄ = inj₂ $ λ where 
    ⟨ there k₁∈kvs ⟩ → k<l→k∉kvs k₁ kvs ⟨ k₁∈kvs ⟩
    ⟨ here ⟩         → <antisym {K +∞} k₁<k₂ refl
  ... | GT ⦃ k₁>k₂ ⦄ with k₁ ∈? kvs
  ... | inj₁ ⟨ k₁∈kvs ⟩ = inj₁ ⟨ there k₁∈kvs ⟩ 
  ... | inj₂ k₁∉kvs = inj₂ $ λ where 
    ⟨ there k₁∈kvs ⟩ → k₁∉kvs ⟨ k₁∈kvs ⟩
    ⟨ here ⟩         → <antisym {K +∞} k₁>k₂ refl

  insert-com : ∀ {l u : K +∞} (k₁ k₂ : K) (v₁ v₂ : V)
                 ⦃ l<k₁ : l < inj k₁ ⦄ ⦃ k₁<u : inj k₁ < u ⦄
                 ⦃ l<k₂ : l < inj k₂ ⦄ ⦃ k₂<u : inj k₂ < u ⦄ 
                 (kvs : OFM V l u)
            → (k₁ ≡ k₂ → v₁ ≡ v₂)
            → insert k₁ v₁ (insert k₂ v₂ kvs) ≡ insert k₂ v₂ (insert k₁ v₁ kvs)

  insert-com-lemma-1a : ∀ {l u : K +∞} 
                          (k₁ k₂ k₃ : K) (v₁ v₂ v₃ : V) (kvs : OFM V (inj k₃) u)
                          ⦃ _ : inj k₁ < u ⦄      ⦃ _ : inj k₂ < u ⦄
                          ⦃ _ : inj k₁ < inj k₂ ⦄ ⦃ _ : inj k₂ < inj k₃ ⦄
                          ⦃ _ : l < inj k₁ ⦄ ⦃ _ : l < inj k₂ ⦄ 
                          ⦃ _ : l < inj k₃ ⦄
                      → insert {l = l} k₁ v₁ (k₂ ↦ v₂ ∷ k₃ ↦ v₃ ∷ kvs) 
                      ≡ insert         k₂ v₂ (insert k₁ v₁ (k₃ ↦ v₃ ∷ kvs))
  insert-com-lemma-1a k₁ k₂ k₃ v₁ v₂ v₃ kvs ⦃ _ ⦄ ⦃ _ ⦄ ⦃ k₁<k₂ ⦄ ⦃ k₂<k₃ ⦄ 
    rewrite compare-coh< {K +∞} $ <trans {K +∞} k₁<k₂ k₂<k₃
    rewrite compare-coh< {K +∞} k₁<k₂ rewrite compare-coh> {K +∞} k₁<k₂
    rewrite compare-coh< {K +∞} k₂<k₃
    = refl

  insert-com-lemma-1b : ∀ {l u : K +∞} 
                          (k₁ k₂ k₃ : K) (v₁ v₂ v₃ : V) (kvs : OFM V (inj k₃) u)
                          ⦃ _ : inj k₁ < inj k₂ ⦄ ⦃ _ : inj k₃ < inj k₂ ⦄
                          ⦃ _ : inj k₁ < u ⦄      ⦃ _ : inj k₂ < u ⦄
                          ⦃ _ : l < inj k₁ ⦄ ⦃ _ : l < inj k₂ ⦄ 
                          ⦃ _ : l < inj k₃ ⦄ 
                      → (k₁ ≡ k₂ → v₁ ≡ v₂)
                      → insert {l = l} k₁ v₁ (k₃ ↦ v₃ ∷ insert k₂ v₂ kvs)
                      ≡ insert         k₂ v₂ (insert k₁ v₁ (k₃ ↦ v₃ ∷ kvs))
  insert-com-lemma-1b k₁ k₂ k₃ v₁ v₂ v₃ kvs ⦃ k₁<k₂ ⦄ ⦃ k₂>k₃ ⦄ p 
    with compare (inj k₁) (inj k₃) 
  ... | GT rewrite compare-coh> {K +∞} k₂>k₃ rewrite compare-coh< {K +∞} k₁<k₂ 
    = cong (λ kvs → k₃ ↦ v₃ ∷ kvs) $ insert-com k₁ k₂ v₁ v₂ kvs p
  ... | LT rewrite compare-coh> {K +∞} k₁<k₂ rewrite compare-coh> {K +∞} k₂>k₃
    = refl
  ... | EQ rewrite compare-coh> {K +∞} k₁<k₂ rewrite uo<p {K +∞} k₁<k₂ k₂>k₃ 
    = refl

  insert-com-lemma-2 : ∀ {l u : K +∞} 
                         (k₁ k₂ k₃ : K) (v₁ v₂ v₃ : V) (kvs : OFM V (inj k₃) u)
                         ⦃ _ : inj k₁ < inj k₂ ⦄ 
                         ⦃ _ : l < inj k₁ ⦄ ⦃ _ : inj k₁ < u ⦄
                         ⦃ _ : l < inj k₂ ⦄ ⦃ _ : inj k₂ < u ⦄ 
                         ⦃ _ : l < inj k₃ ⦄ 
                     → (k₁ ≡ k₂ → v₁ ≡ v₂)
                     → insert {l = l} k₁ v₁ (insert k₂ v₂ (k₃ ↦ v₃ ∷ kvs)) 
                     ≡ insert         k₂ v₂ (insert k₁ v₁ (k₃ ↦ v₃ ∷ kvs))
  insert-com-lemma-2 k₁ k₂ k₃ v₁ v₂ v₃ kvs ⦃ k₁<k₂ ⦄ p
      with compare (inj k₂) (inj k₃) 
  ... | LT = insert-com-lemma-1a k₁ k₂ k₃ v₁ v₂ v₃ kvs
  ... | GT = insert-com-lemma-1b k₁ k₂ k₃ v₁ v₂ v₃ kvs p
  ... | EQ rewrite compare-coh< {K +∞} k₁<k₂ rewrite compare-coh> {K +∞} k₁<k₂ 
          rewrite compare-coh≡ {x = inj k₂}
    = refl

  insert-com k₁ k₂ v₁ v₂ [] p with compare (inj k₁) (inj k₂)
  ... | LT ⦃ k₁<k₂ ⦄ rewrite compare-coh> {K +∞} k₁<k₂ = refl
  ... | GT ⦃ k₁>k₂ ⦄ rewrite compare-coh< {K +∞} k₁>k₂ = refl
  insert-com k₁ k₁ v₁ k₂ ⦃ l<k₁ ⦄ ⦃ k₁<u ⦄ ⦃ l<k₂ ⦄ ⦃ k₂<u ⦄ [] p | EQ
    rewrite compare-coh≡ {x = inj k₁} 
    rewrite uo<p {K +∞} k₁<u k₂<u rewrite uo<p {K +∞} l<k₁ l<k₂ 
    rewrite p refl = refl
  insert-com k₁ k₂ v₁ v₂ ⦃ l<k₁ ⦄ ⦃ k₁<u ⦄ ⦃ l<k₂ ⦄ ⦃ k₂<u ⦄ (k₃ ↦ v₃ ∷ kvs) p 
      with compare (inj k₁) (inj k₂) in cmp-k₁k₂
  ... | LT = insert-com-lemma-2 k₁ k₂ k₃ v₁ v₂ v₃ kvs p 
  ... | GT = sym $ insert-com-lemma-2 k₂ k₁ k₃ v₂ v₁ v₃ kvs $ sym ∘ p ∘ sym
  ... | EQ with compare (inj k₁) (inj k₃) in cmp-k₁k₃
  ... | LT rewrite cmp-k₁k₂ rewrite p refl rewrite uo<p {K +∞} l<k₁ l<k₂
    = refl
  ... | GT rewrite cmp-k₁k₃ rewrite p refl rewrite uo<p {K +∞} k₁<u k₂<u = refl
  ... | EQ rewrite cmp-k₁k₂ rewrite p refl = refl

FinMap : (K V : Set) ⦃ _ : Ord K ⦄ → Set
FinMap K V = OFM {K} V -∞ ∞
