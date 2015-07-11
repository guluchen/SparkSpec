module Reduce where

open import Function
open import Data.Empty
open import Data.Bool using (Bool; true; false; if_then_else_; not; T)
open import Data.Product hiding (map)
open import Data.Sum hiding (map)
open import Data.Nat
open import Data.List
open import Data.List.All hiding (map)
open import Data.List.Any hiding (map)
open import Relation.Nullary
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Relation.Unary using (Decidable)
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning renaming (begin_ to ≡-begin_; _∎ to _≡∎)

open import Spec
open import List+

reduce₁ : {A : Set} → (A → A → A) → (xs : List⁺ A) → A
reduce₁ _⊕_ [ x ]⁺ = x
reduce₁ _⊕_ (x ∷⁺ xs) = x ⊕ reduce₁ _⊕_ xs

reduce : {A : Set} → (A → A → A) → List⁺ (List⁺ A) → A
reduce ⊕ = reduce₁ ⊕ ∘ map⁺ (reduce₁ ⊕)

↾ : {A : Set} → (A → A → A) → (Key × A) → ListK A → ListK A
↾ _⊕_ (k , a) [] = (k , a) ∷ []
↾ _⊕_ (k , a) ((j , a') ∷ xs) with k ≟ j
... | yes _ = (k , a ⊕ a') ∷ xs
... | no  _ = (j , a') ∷ ↾ _⊕_ (k , a) xs

↾⊕-eq : {A : Set} → (_⊕_ : A → A → A)
      → (k : Key) (a₁ a₂ : A) (xs : ListK A)
      → ↾ _⊕_ (k , a₁) ((k , a₂) ∷ xs) ≡ (k , a₁ ⊕ a₂) ∷ xs
↾⊕-eq _⊕_ k a₁ a₂ xs with k ≟ k
... | yes _ = refl
... | no k≠k = ⊥-elim (k≠k refl)

postulate
  repartition : {A : Set} → List A → List (List A)

reduceByKey : {A : Set} → (A → A → A) → List (ListK A) → List (ListK A)
reduceByKey ⊕ =
  repartition ∘ foldr (↾ ⊕) [] ∘ concat ∘ map (foldr (↾ ⊕) [])

select-↾-eq : ∀ {A} (k : Key) (⊕ : A → A → A)
              → (v : A) → (xs : ListK A)
              → filter (keyEq k) (↾ ⊕ (k , v) xs) ≡ ↾ ⊕ (k , v) (filter (keyEq k) xs)
select-↾-eq k ⊕ v [] with k ≟ k
... | yes _ = refl
... | no k≠k = ⊥-elim (k≠k refl)
select-↾-eq k ⊕ v ((j , u) ∷ xs) with k ≟ j
select-↾-eq k ⊕ v ((._ , u) ∷ xs) | yes refl
  with k ≟ k
...   | yes _ = refl
...   | no k≠k = ⊥-elim (k≠k refl)
select-↾-eq k ⊕ v ((j , u) ∷ xs) | no k≠j with k ≟ j
... | yes k≡j = ⊥-elim (k≠j k≡j)
... | no _ = select-↾-eq k ⊕ v xs

select-↾-neq : ∀ {A} (k j : Key) → ¬ (k ≡ j)
             → (⊕ : A → A → A) (v : A) (xs : ListK A)
             → filter (keyEq k) (↾ ⊕ (j , v) xs) ≡ filter (keyEq k) xs
select-↾-neq k j k≠j ⊕ v [] with k ≟ j
... | yes k≡j = ⊥-elim (k≠j k≡j)
... | no  _   = refl
select-↾-neq k j k≠j ⊕ v ((l , u) ∷ xs) with j ≟ l
select-↾-neq k j k≠j ⊕ v ((._ , u) ∷ xs) | yes refl with k ≟ j
... | yes k≡j  = ⊥-elim (k≠j k≡j)
... | no _ = refl
select-↾-neq k j k≠j ⊕ v ((l , u) ∷ xs) | no j≠l with k ≟ l
select-↾-neq k j k≠j ⊕ v ((._ , u) ∷ xs) | no j≠l | yes refl
  rewrite select-↾-neq k j k≠j ⊕ v xs = refl
select-↾-neq k j k≠j ⊕ v ((l , u) ∷ xs) | no j≠l | no _ =
   select-↾-neq k j k≠j ⊕ v xs

select-foldr : ∀ {A} (k : Key) (⊕ : A → A → A)
                → filter (keyEq k) ∘ foldr (↾ ⊕) [] ≗
                         foldr (↾ ⊕) [] ∘ filter (keyEq k)
select-foldr k ⊕ [] = refl
select-foldr k ⊕ ((j , v) ∷ xs) with k ≟ j
select-foldr k ⊕ ((._ , v) ∷ xs) | yes refl =
  ≡-begin
    filter (keyEq k) (foldr _⊕↾_ [] ((k , v) ∷ xs))
  ≡⟨ refl ⟩
    filter (keyEq k) ((k , v) ⊕↾ foldr _⊕↾_ [] xs)
  ≡⟨ select-↾-eq k ⊕ v (foldr _⊕↾_ [] xs) ⟩
    (k , v) ⊕↾ filter (keyEq k) (foldr _⊕↾_ [] xs)
  ≡⟨ cong (_⊕↾_ (k , v)) (select-foldr k ⊕ xs) ⟩
    (k , v) ⊕↾ foldr (↾ ⊕) [] (filter (keyEq k) xs)
  ≡∎
 where _⊕↾_ =  ↾ ⊕
select-foldr k ⊕ ((j , v) ∷ xs) | no k≠j =
  ≡-begin
    filter (keyEq k) (foldr _⊕↾_ [] ((j , v) ∷ xs))
  ≡⟨ refl ⟩
    filter (keyEq k) ((j , v) ⊕↾ foldr _⊕↾_ [] xs)
  ≡⟨ select-↾-neq k j k≠j ⊕ v (foldr _⊕↾_ [] xs) ⟩
    filter (keyEq k) (foldr _⊕↾_ [] xs)
  ≡⟨ select-foldr k ⊕ xs ⟩
    foldr (↾ ⊕) [] (filter (keyEq k) xs)
  ≡∎
 where _⊕↾_ =  ↾ ⊕


data Any! {A : Set} (P : A → Set) : List A → Set where
   here : ∀ {x xs} → P x → All (¬_ ∘ P) xs → Any! P (x ∷ xs)
   there : ∀ {x xs} → Any! P xs → Any! P (x ∷ xs)

filter⁺ : {A : Set} {P : A → Set} → Decidable P → (xs : List A) → (Any! P xs) → List⁺ A
filter⁺ p [] ()
filter⁺ p (x ∷ xs) (here _ _) = [ x ]⁺
filter⁺ p (x ∷ xs) (there p∈) with p x
... | yes _ = x ∷⁺ filter⁺ p xs p∈
... | no ¬p = filter⁺ p xs p∈

KeyEq : ∀ {A} (k : Key) → (Key × A) → Set
KeyEq k = _≡_ k ∘ key

keyEq? : ∀ {A} k → Decidable (KeyEq {A} k)
keyEq? k = _≟_ k ∘ key

postulate
 filter-eq : ∀ {A} k (v : A) xs →
  filter (keyEq k) ((k , v) ∷ xs) ≡ (k , v) ∷ filter (keyEq k) xs

foldr-↾-reduce : ∀ {A} (k : Key) (⊙ : A → A → A) (xs : ListK A)
   → (k∈ : Any! (KeyEq k) xs)
   → foldr (↾ ⊙) [] (filter (keyEq k) xs) ≡
       (k , reduce₁ ⊙ (map⁺ value (filter⁺ (keyEq? k) xs k∈))) ∷ []
foldr-↾-reduce k ⊕ [] ()
foldr-↾-reduce k ⊕ ((._ , v) ∷ xs) (here refl k∉) =
  ≡-begin
    foldr (↾ ⊕) [] (filter (keyEq k) ((k , v) ∷ xs))
  ≡⟨ cong (foldr (↾ ⊕) []) (filter-eq k v xs) ⟩
    (k , v) ⊕↾ foldr (↾ ⊕) [] (filter (keyEq k) xs)
  ≡⟨ cong (_⊕↾_ (k , v)) lemma ⟩
   (k , v) ⊕↾ []
  ≡∎
 where _⊕↾_ =  ↾ ⊕
       postulate
        lemma : foldr (↾ ⊕) [] (filter (keyEq k) xs) ≡ []
foldr-↾-reduce k ⊕ ((j , v) ∷ xs) (there k∈) with k ≟ j
foldr-↾-reduce k ⊕ ((._ , v) ∷ xs) (there k∈) | yes refl =
  ≡-begin
    (k , v) ⊕↾ foldr (↾ ⊕) [] (filter (keyEq k) xs)
  ≡⟨ cong (_⊕↾_ (k , v)) (foldr-↾-reduce k ⊕ xs k∈) ⟩
    (k , v) ⊕↾ ((k , reduce₁ ⊕ (map⁺ value (filter⁺ (keyEq? k) xs k∈))) ∷ [])
  ≡⟨ ↾⊕-eq ⊕ k v _ [] ⟩
    (k , ⊕ v (reduce₁ ⊕ (map⁺ value (filter⁺ (keyEq? k) xs k∈)))) ∷ []
  ≡∎
 where _⊕↾_ =  ↾ ⊕
foldr-↾-reduce k ⊕ ((j , v) ∷ xs) (there k∈) | no k≠j =
   foldr-↾-reduce k ⊕ xs k∈

head' : {A : Set} → A → List A → A
head' z [] = z
head' z (x ∷ _) = x

head-red-↾ : ∀ {A} k (z : A) (⊙ : A → A → A) (xs : ListK A)
           → (k∈ : Any! (KeyEq k) xs)
           → (head' z ∘ map value ∘ foldr (↾ ⊙) [] ∘ filter (keyEq k) $ xs)
                   ≡ (reduce₁ ⊙ ∘ map⁺ value $ filter⁺ (keyEq? k) xs k∈)
head-red-↾ k z ⊙ xs k∈ =
  ≡-begin
    (head' z ∘ map value ∘ foldr (↾ ⊙) [] ∘ filter (keyEq k) $ xs)
  ≡⟨ cong (head' z ∘ map value) (foldr-↾-reduce k ⊙ xs k∈) ⟩
   (head' z ∘ map value $ (k , reduce₁ ⊙ (map⁺ value (filter⁺ (keyEq? k) xs k∈))) ∷ [])
  ≡⟨ refl ⟩
   reduce₁ ⊙ (map⁺ value (filter⁺ (keyEq? k) xs k∈))
  ≡∎

 -- filter-¬null = filter (¬ ∘ null)

filter-¬null : {A : Set} (xss : List (List A)) → Any! (¬_ ∘ (_≡_ [])) xss → List⁺ (List⁺ A)
filter-¬null [] ()
filter-¬null (xs ∷ xss) (here nxs _) = [ List→List⁺ xs nxs ]⁺
filter-¬null ([] ∷ xss) (there ne) = filter-¬null xss ne
filter-¬null ((x ∷ xs) ∷ xss) (there ne) =
   List→List⁺ (x ∷ xs) (λ ()) ∷⁺ filter-¬null xss ne

concat⁺' : {A : Set} (xss : List (List A)) → Any! (¬_ ∘ (_≡_ [])) xss → List⁺ A
concat⁺' [] ()
concat⁺' (xs ∷ xss) (here nxs _) = List→List⁺ xs nxs
concat⁺' (xs ∷ xss) (there ne) = xs ++⁺ concat⁺' xss ne

postulate
 mapred-select : ∀ {A} (k : Key) (⊙ : A → A → A) →
     ∀ xss
     → (ne₁ : Any! (¬_ ∘ _≡_ [])
          (map (map value ∘ filter (keyEq k) ∘ foldr (↾ ⊙) []) $ xss))
     → (ne₂ : Any! (¬_ ∘ _≡_ []) (map (map value ∘ filter (keyEq k)) $ xss))
     → concat⁺' (map (map value ∘ filter (keyEq k) ∘ foldr (↾ ⊙) []) $ xss) ne₁  ≡
         map⁺ (reduce₁ ⊙) (filter-¬null
            (map (map value ∘ filter (keyEq k)) $ xss) ne₂)
-- mapred-select k ⊙ [] () _
-- mapred-select k ⊙ (xs ∷ xss) ne₁ ne₂ = {!   !}


reduceWithKey : {A : Set} → (k : Key) → (A → A → A)
              → (xss : List (ListK A))
              → Any! (¬_ ∘ _≡_ []) (map (map value ∘ filter (keyEq k)) xss) → A
reduceWithKey k ⊕ xss ne =
  reduce ⊕ $
    filter-¬null
      (map (map value ∘ filter (keyEq k)) xss)
      ne

lookUp : ∀ {A} → Key → A → List (ListK A) → A
lookUp k z = head' z ∘ concat ∘ map (map value ∘ filter (keyEq k))


-- naturalty laws we assume of repartition
postulate
  repart-filter : {A : Set} (p : A → Bool) →
     repartition ∘ filter p ≗ map (filter p) ∘ repartition
  repart-map : {A B : Set} (f : A → B) →
     repartition ∘ map f ≗ map (map f) ∘ repartition
  concat-repart : {A : Set} (xs : List A) →
     concat (repartition xs) ≡ xs

-- other routine naturalty laws
postulate
  map-map : {A B C : Set} (f : B → C) (g : A → B)
          → map f ∘ map g ≗ map (f ∘ g)
  filter-concat : {A : Set} (p : A → Bool)
          → filter p ∘ concat ≗ concat ∘ map (filter p)
  map-concat : {A B : Set} (f : A → B)
          → map f ∘ concat ≗ concat ∘ map (map f)

reduceBy-reduceWith :
  ∀ {A} (k : Key) (z : A) (⊕ : A → A → A)
  → (xss : List (ListK A))
  → (ne : Any! (¬_ ∘ _≡_ []) (map (map value ∘ filter (keyEq k)) xss))
  → lookUp k z (reduceByKey ⊕ xss) ≡ (reduceWithKey k ⊕ xss ne)
reduceBy-reduceWith k z ⊕ xss ne₃ =
  ≡-begin
    lookUp k z (reduceByKey ⊕ xss)
  ≡⟨ refl ⟩
    (head' z ∘ concat ∘ map (map value ∘ filter (keyEq k)) ∘
       repartition ∘ foldr (↾ ⊕) [] ∘ concat ∘ map (foldr (↾ ⊕) []) $ xss)
  ≡⟨ cong (head' z) (naturalty₁ value (keyEq k) _) ⟩
    (head' z ∘ map value ∘ filter (keyEq k) ∘ foldr ↾⊕ [] ∘
       concat ∘ map (foldr ↾⊕ []) $ xss)
  ≡⟨ cong (head' z ∘ map value) (select-foldr k ⊕ (concat ∘ map (foldr ↾⊕ []) $ xss)) ⟩
    (head' z ∘ map value ∘ foldr ↾⊕ [] ∘ filter (keyEq k) ∘
       concat ∘ map (foldr ↾⊕ []) $ xss)
  ≡⟨ head-red-↾ k z ⊕ (concat ∘ map (foldr ↾⊕ []) $ xss) ne₁ ⟩
    (reduce₁ ⊕ ∘ map⁺ value $ filter⁺ (keyEq? k)
             (concat ∘ map (foldr ↾⊕ []) $ xss) ne₁ )
  ≡⟨ cong (reduce₁ ⊕) (naturalty₂ value k (foldr ↾⊕ []) xss ne₁ ne₂) ⟩
    reduce₁ ⊕ (concat⁺'
        (map (map value ∘ filter (keyEq k) ∘ foldr ↾⊕ []) xss) ne₂)
  ≡⟨ cong (reduce₁ ⊕) (mapred-select k ⊕ xss ne₂ ne₃) ⟩
    reduce₁ ⊕ (map⁺ (reduce₁ ⊕) (filter-¬null
        (map (map value ∘ filter (keyEq k)) xss) ne₃))
  ≡⟨ refl ⟩
    reduceWithKey k ⊕ xss ne₃
  ≡∎

 where
  ↾⊕ = ↾ ⊕

  postulate
    ne₁ : Any! (KeyEq k) (concat (map (foldr (↾ ⊕) []) xss))
    ne₂ : Any! (¬_ ∘ _≡_ [])
           (map (map value ∘ filter (keyEq k) ∘ foldr (↾ ⊕) []) xss)

  naturalty₁ : {A B : Set} (f : A → B) (p : A → Bool) →
        concat ∘ map (map f ∘ filter p) ∘ repartition ≗ map f ∘ filter p
  naturalty₁ f p xss =
      ≡-begin
       (concat ∘ map (map f ∘ filter p) ∘ repartition $ xss)
      ≡⟨ cong concat (sym (map-map (map f) (filter p) (repartition xss))) ⟩
       (concat ∘ map (map f) ∘ map (filter p) ∘ repartition $ xss)
      ≡⟨ cong (concat ∘ map (map f)) (sym (repart-filter p xss)) ⟩
       (concat ∘ map (map f) ∘ repartition ∘ filter p $ xss)
      ≡⟨ cong concat (sym (repart-map f _)) ⟩
       (concat ∘ repartition ∘ map f ∘ filter p $ xss)
      ≡⟨ concat-repart _ ⟩
       (map f ∘ filter p $ xss)
      ≡∎

  postulate
   naturalty₂ : {A B C : Set} (f : (Key × A) → B)
              → (k : Key) (g : List C → List (Key × A))
              → (xss : List (List C))
              → (ne₁ : Any! (KeyEq k) (concat (map g xss)))
              → (ne₂ : Any! (¬_ ∘ _≡_ []) (map (map f ∘ filter (keyEq k) ∘ g) xss))
              → map⁺ f (filter⁺ (keyEq? k) (concat (map g xss)) ne₁) ≡
                 concat⁺' (map (map f ∘ filter (keyEq k) ∘ g) xss) ne₂
