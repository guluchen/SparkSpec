module Homomorphism where

open import Data.Product
open import Data.List
open import Relation.Unary
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

IsHom : {A B : Set} → (h : List A → B)
      → (_⊕_ : B → B → B) → (z : B)
      → Set
IsHom h _⊕_ z =
  (h [] ≡ z) ×
  (∀ {xs ys} → h (xs ++ ys) ≡ h xs ⊕ h ys)

ran : {A B : Set} → (A → B) → B → Set
ran f b = ∃ (λ a → f a ≡ b)

hom⇒identity-l : ∀ {A B} {h : List A → B} {_⊕_} {z}
               → IsHom h _⊕_ z
               → (∀ {b} → b ∈ ran h → z ⊕ b ≡ b)
hom⇒identity-l {h = h} {_⊕_} {z} (h[] , h++) {b} (xs , hxs≡b) =
  begin
     z ⊕ b
  ≡⟨ cong (_⊕_ z) (sym hxs≡b) ⟩
     z ⊕ h xs
  ≡⟨ cong (λ c → c ⊕ h xs) (sym h[]) ⟩
     h [] ⊕ h xs
  ≡⟨ sym h++ ⟩
     h ([] ++ xs)
  ≡⟨ refl ⟩
     h xs
  ≡⟨ hxs≡b ⟩
     b
  ∎

hom⇒identity-r : ∀ {A B} {h : List A → B} {_⊕_} {z}
                 → IsHom h _⊕_ z
                 → (∀ {b} → b ∈ ran h → b ⊕ z ≡ b)
hom⇒identity-r {h = h} {_⊕_} {z} (h[] , h++) {b} (xs , hxs≡b) =
    begin
       b ⊕ z
    ≡⟨ cong (λ b → b ⊕ z) (sym hxs≡b) ⟩
       h xs ⊕ z
    ≡⟨ cong (λ c → h xs ⊕ c) (sym h[]) ⟩
       h xs ⊕ h []
    ≡⟨ sym h++ ⟩
       h (xs ++ [])
    ≡⟨ cong h []-right-id ⟩
       h xs
    ≡⟨ hxs≡b ⟩
       b
    ∎
  where []-right-id : {A : Set} {xs : List A} → xs ++ [] ≡ xs
        []-right-id {xs = []} = refl
        []-right-id {xs = x ∷ xs} rewrite []-right-id {xs = xs} = refl

hom⇒assoc : ∀ {A B} {h : List A → B} {_⊕_} {z}
            → IsHom h _⊕_ z
            → (∀ {a b c} → a ∈ ran h → b ∈ ran h → c ∈ ran h
               → (a ⊕ (b ⊕ c)) ≡ ((a ⊕ b) ⊕ c))
hom⇒assoc {A}{h = h} {_⊕_} {z} (h[] , h++)
          (xs , refl) (ys , refl) (zs , refl) =
  begin
    h xs ⊕ (h ys ⊕ h zs)
  ≡⟨ cong (_⊕_ (h xs)) (sym h++) ⟩
    h xs ⊕ h (ys ++ zs)
  ≡⟨ sym h++ ⟩
    h (xs ++ ys ++ zs)
  ≡⟨ cong h (assoc xs ys zs) ⟩
    h ((xs ++ ys) ++ zs)
  ≡⟨ h++ ⟩
   h (xs ++ ys) ⊕ h zs
  ≡⟨ cong (λ b → b ⊕ h zs) h++ ⟩
   (h xs ⊕ h ys) ⊕ h zs
  ∎
 where
  assoc : ∀ {A : Set} (xs : List A) ys zs
        → xs ++ (ys ++ zs) ≡ (xs ++ ys) ++ zs
  assoc []       ys zs = refl
  assoc (x ∷ xs) ys zs = cong (_∷_ x) (assoc xs ys zs)
