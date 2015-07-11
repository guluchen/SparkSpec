module Deterministic where

open import Function
open import Data.Product hiding (map)
open import Data.List
open import Relation.Binary.PropositionalEquality

data Ins {A : Set} : A → List A → List A → Set where
  here  : ∀ {x xs} → Ins x xs (x ∷ xs)
  there : ∀ {x y xs xs'} → Ins y xs xs' → Ins y (x ∷ xs) (x ∷ xs')

data Perm {A : Set} : List A → List A → Set where
  nil  : Perm [] []
  cons : ∀ {x xs ys zs} → Perm xs ys → Ins x ys zs → Perm (x ∷ xs) zs 

RePart : {A : Set} → List (List A) → List (List A) → Set
RePart xss yss = ∃ (λ zss → Perm yss zss × (concat xss ≡ concat zss))

Det : {A B : Set} → (List (List A) → B) → Set
Det h = ∀ {xss yss}
        → RePart xss yss
        → h xss ≡ h yss
        
aggregate : {A B : Set} → B → (A → B → B) → (B → B → B) → List (List A) → B
aggregate z ⊗ ⊕ = foldr ⊕ z ∘ map (foldr ⊗ z)

---

-- → (∀ {b} → b ∈ ran h → z ⊕ b ≡ b)

{-
    z ⊕ b 
  = z ⊕ 
-}
