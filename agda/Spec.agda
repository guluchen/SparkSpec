module Spec where

open import Function
open import Data.Bool using (Bool; if_then_else_; not)
open import Data.Product hiding (map)
open import Data.Nat using (ℕ; _≟_)
open import Data.List
open import Relation.Nullary.Decidable using (⌊_⌋)

Partition : Set → Set
Partition A = List A

RDD : Set → Set
RDD A = List (Partition A)

postulate
  perm : {A : Set} → List A → List A

map! : {A B : Set} → (A → B) → List A → List B
map! f = map f ∘ perm


key : {A B : Set} → (A × B) → A
key = proj₁

value : {A B : Set} → (A × B) → B
value = proj₂

Key : Set
Key = ℕ

ListK : Set → Set
ListK A = List (Key × A)

keyEq : Key → {A : Set} → (Key × A) → Bool
keyEq k kv = ⌊ k ≟ key kv ⌋

PairRDD : Set → Set → Set
PairRDD A B = RDD (A × B)

hasValue : ∀ {A} → Key → A → ListK A → A
hasValue k z = foldr (λ kv r → if keyEq k kv then value kv else r) z

addTo : ∀ {A} → Key → A → ListK A → ListK A
addTo k v ps = (k , v) ∷ filter (keyEq k) ps
