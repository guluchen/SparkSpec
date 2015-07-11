module Aggregate where

open import Function
open import Data.Empty
open import Data.Bool using (Bool; if_then_else_; not)
open import Data.Product hiding (map)
open import Data.Sum hiding (map)
open import Data.Nat
open import Data.List
open import Data.List.All hiding (map)
open import Data.List.Any hiding (map)
open import Relation.Nullary
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning renaming (begin_ to ≡-begin_; _∎ to _≡∎)

open import Spec

aggregate : {A B : Set} → B → (A → B → B) → (B → B → B) -> RDD A -> B
aggregate z ⊗ ⊕ = foldr ⊕ z ∘ map! (foldr ⊗ z)

↾ : {A B : Set} → (A → B → B) → B → (Key × A) → ListK B → ListK B
↾ _⊕_ z (k , a) [] = (k , a ⊕ z) ∷ []
↾ _⊕_ z (k , a) ((j , a') ∷ xs) with k ≟ j
... | yes _ = (k , a ⊕ a') ∷ xs
... | no  _ = (j , a') ∷ ↾ _⊕_ z (k , a) xs

↾⊕-eq : {A B : Set} → (_⊕_ : A → B → B) (z : B)
      → (k : Key) (a : A) (b : B) (xs : ListK B)
      → ↾ _⊕_ z (k , a) ((k , b) ∷ xs) ≡ (k , a ⊕ b) ∷ xs
↾⊕-eq _⊕_ z k a b xs with k ≟ k
... | yes _ = refl
... | no k≠k = ⊥-elim (k≠k refl)

postulate
  repartition : {A : Set} → List A → List (List A)

aggregateByKey : ∀ {A B} → B → (A → B → B) → (B → B → B)
                → PairRDD Key A → PairRDD Key B
aggregateByKey z ⊗ ⊕ =
  repartition ∘ foldr (↾ ⊕ z) [] ∘ concat ∘ map! (foldr (↾ ⊗ z) [])

aggregateWithKey : ∀ {A B} → Key → B → (A → B → B) → (B → B → B)
                 → PairRDD Key A → B
aggregateWithKey k z ⊗ ⊕ =
  aggregate z ⊗ ⊕ ∘ filter (not ∘ null) ∘
    map (map value ∘ filter (keyEq k))


head' : {A : Set} → A → List A → A
head' z [] = z
head' z (x ∷ _) = x

lookUp : ∀ {A} → Key → A → PairRDD Key A → A
lookUp k z = head' z ∘ concat ∘ map (map value ∘ filter (keyEq k))

lookUpL : ∀ {A} → Key → A → ListK A → A
lookUpL k z = head' z ∘ map value ∘ filter (keyEq k)

---


select-↾-eq : ∀ {A B} (k : Key) (⊕ : A → B → B) (z : B)
            → (v : A) → (xs : ListK B)
            → filter (keyEq k) (↾ ⊕ z (k , v) xs) ≡ ↾ ⊕ z (k , v) (filter (keyEq k) xs)
select-↾-eq k ⊕ z v [] with k ≟ k
... | yes _ = refl
... | no ¬p = ⊥-elim (¬p refl)
select-↾-eq k ⊕ z v ((j , u) ∷ xs) with k ≟ j
select-↾-eq k ⊕ z v ((._ , u) ∷ xs) | yes refl with k ≟ k
...         | yes _ = refl
...         | no ¬p = ⊥-elim (¬p refl)
select-↾-eq k ⊕ z v ((j , u) ∷ xs) | no ¬p with k ≟ j
... | yes q = ⊥-elim (¬p q)
... | no _  = select-↾-eq k ⊕ z v xs


select-↾-neq : ∀ {A B} (k j : Key) → ¬ (k ≡ j)
            → (⊕ : A → B → B) (z : B)
            → (v : A) → (xs : ListK B)
            → filter (keyEq k) (↾ ⊕ z (j , v) xs) ≡ filter (keyEq k) xs
select-↾-neq k j k≠j ⊕ z v [] with  k ≟ j
... | yes k≡j = ⊥-elim (k≠j k≡j)
... | no   _ = refl
select-↾-neq k j j≠k ⊕ z v ((l , u) ∷ xs) with j ≟ l
select-↾-neq k j j≠k ⊕ z v ((._ , u) ∷ xs) | yes refl with k ≟ j
... | yes j≡k = ⊥-elim (j≠k j≡k)
... | no  _ = refl
select-↾-neq k j j≠k ⊕ z v ((l , u) ∷ xs)  | no l≠j with k ≟ l
select-↾-neq k j j≠k ⊕ z v ((._ , u) ∷ xs)  | no l≠j | yes refl
  rewrite select-↾-neq k j j≠k ⊕ z v xs = refl
select-↾-neq k j j≠k ⊕ z v ((l , u) ∷ xs)  | no l≠j | no _ =
  select-↾-neq k j j≠k ⊕ z v xs

select-foldr : ∀ {A B} (k : Key)
             → (⊕ : A → B → B) (z : B)
             → filter (keyEq k) ∘ foldr (↾ ⊕ z) [] ≗
                      foldr (↾ ⊕ z) [] ∘ filter (keyEq k)
select-foldr k ⊕ z [] = refl
select-foldr k ⊕ z ((j , v) ∷ xs) with k ≟ j
select-foldr k ⊕ z ((._ , v) ∷ xs) | yes refl =
   ≡-begin
     filter (keyEq k) (foldr _⊕↾_ [] ((k , v) ∷ xs))
   ≡⟨ refl ⟩
     filter (keyEq k) ((k , v) ⊕↾ (foldr (↾ ⊕ z) [] xs))
   ≡⟨ select-↾-eq k ⊕ z v (foldr (↾ ⊕ z) [] xs) ⟩
     (k , v) ⊕↾ (filter (keyEq k) (foldr _⊕↾_ [] xs))
   ≡⟨ cong (λ ys → (k , v) ⊕↾ ys) (select-foldr k ⊕ z xs) ⟩
     (k , v) ⊕↾ (foldr _⊕↾_ [] (filter (keyEq k) xs))
-- ≡ foldr (↾ ⊕ z) [] (filter (keyEq k) ((k , v) ∷ xs)), expanded already
   ≡∎
 where _⊕↾_ =  ↾ ⊕ z
select-foldr k ⊕ z ((j , v) ∷ xs) | no k≠j =
   ≡-begin
     filter (keyEq k) (foldr _⊕↾_ [] ((j , v) ∷ xs))
   ≡⟨ refl ⟩
     filter (keyEq k) ((j , v) ⊕↾ foldr _⊕↾_ [] xs)
   ≡⟨ select-↾-neq k j k≠j ⊕ z v (foldr _⊕↾_ [] xs)  ⟩
     filter (keyEq k) (foldr _⊕↾_ [] xs)
   ≡⟨ select-foldr k ⊕ z xs ⟩
     foldr (↾ ⊕ z) [] (filter (keyEq k) xs)
-- ≡ foldr (↾ ⊕ z) [] (filter (keyEq k) ((j , v) ∷ xs)), expanded
   ≡∎
 where _⊕↾_ =  ↾ ⊕ z

postulate
 key-search : ∀ {A} (xs : ListK A) (k : Key)
            → (Any (_≡_ k ∘ key) xs ⊎ All (¬_ ∘ _≡_ k ∘ key) xs)

 filter-neq : ∀ {A} (xs : ListK A) (k : Key)
            → All (¬_ ∘ _≡_ k ∘ key) xs
            → filter (keyEq k) xs ≡ []

foldr-↾-foldr :
  ∀ {A B} (k : Key) (⊙ : A → B → B) (z : B)
    (xs : ListK A)
  → Any (_≡_ k ∘ key) xs
  → foldr (↾ ⊙ z) [] (filter (keyEq k) xs) ≡
      (k , foldr ⊙ z (map value (filter (keyEq k) xs))) ∷ []
foldr-↾-foldr k ⊙ z [] ()
foldr-↾-foldr k ⊙ z ((j , v) ∷ xs) k∈ with k ≟ j
foldr-↾-foldr k ⊙ z ((j , v) ∷ xs) (here k≡j) | no k≠j = ⊥-elim (k≠j k≡j)
foldr-↾-foldr k ⊙ z ((j , v) ∷ xs) (there k∈) | no k≠j =
  foldr-↾-foldr k ⊙ z xs k∈
foldr-↾-foldr k _⊙_ z ((._ , v) ∷ xs) k∈ | yes refl with
   key-search xs k
... | inj₁ k∈' =
   ≡-begin
     (k , v) ⊙↾ foldr _⊙↾_ [] (filter (keyEq k) xs)
   ≡⟨ cong (_⊙↾_ (k , v)) (foldr-↾-foldr k _⊙_ z xs k∈') ⟩
     (k , v) ⊙↾
       ((k , foldr _⊙_ z (map value (filter (keyEq k) xs))) ∷ [])
   ≡⟨ ↾⊕-eq _⊙_ z k v _ [] ⟩
     (k , v ⊙ foldr _⊙_ z (map value (filter (keyEq k) xs))) ∷ []
   ≡∎
 where _⊙↾_ =  ↾ _⊙_ z
... | inj₂ k∉  =
  ≡-begin
    (k , v) ⊙↾ foldr _⊙↾_ [] (filter (keyEq k) xs)
  ≡⟨ cong (λ ys → (k , v) ⊙↾ foldr _⊙↾_ [] ys) (filter-neq xs k k∉) ⟩
    (k , v) ⊙↾ []
  ≡⟨ refl ⟩
    (k , v ⊙ z) ∷ []
  ≡⟨ sym (cong (λ ys → (k , v ⊙ foldr _⊙_ z (map value ys)) ∷ [])
         (filter-neq xs k k∉)) ⟩
    (k , v ⊙ foldr _⊙_ z (map value (filter (keyEq k) xs))) ∷ []
  ≡∎
 where _⊙↾_ =  ↾ _⊙_ z

postulate
 foldr-↾-foldr-¬∃ :
  ∀ {A B} (k : Key) (⊙ : A → B → B) (z : B)
    (xs : ListK A)
  → All (¬_ ∘ _≡_ k ∘ key) xs
  → foldr (↾ ⊙ z) [] (filter (keyEq k) xs) ≡ []

head-foldr-↾ : ∀{A B} k (z : B) (⊙ : A → B → B)
             → head' z ∘ map value ∘ foldr (↾ ⊙ z) [] ∘ filter (keyEq k)
                ≗ foldr ⊙ z ∘ map value ∘ filter (keyEq k)
head-foldr-↾ k z ⊙ xs with key-search xs k
... | inj₁ k∈ =
  ≡-begin
    (head' z ∘ map value ∘ foldr (↾ ⊙ z) [] ∘ filter (keyEq k) $ xs)
  ≡⟨ cong (head' z ∘ map value) (foldr-↾-foldr k ⊙ z xs k∈) ⟩
     head' z (map value
       ((k , foldr ⊙ z (map value (filter (keyEq k) xs))) ∷ []))
  ≡⟨ refl ⟩
     foldr ⊙ z (map value (filter (keyEq k) xs))
  ≡∎
... | inj₂ k∉ rewrite filter-neq xs k k∉ = refl


mapfold-select : ∀ {A B} (k : Key) (z : B) (⊙ : A → B → B) →
  concat ∘ map (map value ∘ filter (keyEq k) ∘ foldr (↾ ⊙ z) []) ≗
    map (foldr ⊙ z) ∘ filter (not ∘ null) ∘
       map (map value ∘ filter (keyEq k))
mapfold-select k z ⊙ [] = refl
mapfold-select k z _⊙_ (xs ∷ xss) =
  ≡-begin
    (concat ∘ map (map value ∘ filter (keyEq k) ∘ foldr _⊙↾_ []) $ xs ∷ xss)
  ≡⟨ refl ⟩
    (map value ∘ filter (keyEq k) ∘ foldr _⊙↾_ [] $ xs) ++
      (concat ∘ map (map value ∘ filter (keyEq k) ∘ foldr _⊙↾_ []) $ xss)
  ≡⟨ cong (_++_ (map value ∘ filter (keyEq k) ∘ foldr _⊙↾_ [] $ xs))
     (mapfold-select k z _⊙_ xss) ⟩
    (map value ∘ filter (keyEq k) ∘ foldr _⊙↾_ [] $ xs) ++
    (map (foldr _⊙_ z) ∘ filter (not ∘ null) ∘
       map (map value ∘ filter (keyEq k)) $ xss)
  ≡⟨ cong cxt₁ (select-foldr k _⊙_ z xs) ⟩
    (map value ∘ foldr _⊙↾_ [] ∘ filter (keyEq k) $ xs) ++
    (map (foldr _⊙_ z) ∘ filter (not ∘ null) ∘
       map (map value ∘ filter (keyEq k)) $ xss)
  ≡⟨ branch (key-search xs k) ⟩
    (map (foldr _⊙_ z) ∘
         filter (not ∘ null) ∘ map (map value ∘ filter (keyEq k))
              $ xs ∷ xss)
  ≡∎
 where
  _⊙↾_ =  ↾ _⊙_ z
  cxt₁ = λ ys → map value ys ++
                    (map (foldr _⊙_ z) ∘ filter (not ∘ null) ∘
                        map (map value ∘ filter (keyEq k)) $ xss)

  postulate
     filter-¬null-filter-keyEq :
         ∀ {A} (k : Key) (xs : ListK A) → Any (λ x → k ≡ proj₁ x) xs → ∀ yss
         → filter (not ∘ null)
             (map value (filter (keyEq k) xs) ∷ yss) ≡
           map value (filter (keyEq k) xs) ∷ filter (not ∘ null) yss
     filter-keyEq-̸¬∃ :
       ∀ {A} (k : Key) (xs : ListK A) → All (¬_ ∘ _≡_ k ∘ key) xs → ∀ yss
       → filter (not ∘ null)
           (map value (filter (keyEq k) xs) ∷ yss) ≡
           filter (not ∘ null) yss

  branch : (Any (_≡_ k ∘ key) xs ⊎ All (¬_ ∘ _≡_ k ∘ key) xs)
    → (map value ∘ foldr _⊙↾_ [] ∘ filter (keyEq k) $ xs) ++
       (map (foldr _⊙_ z) ∘ filter (not ∘ null) ∘
         map (map value ∘ filter (keyEq k)) $ xss)
       ≡ (map (foldr _⊙_ z) ∘
          filter (not ∘ null) ∘ map (map value ∘ filter (keyEq k))
             $ xs ∷ xss)
  branch (inj₁ k∈) =
    ≡-begin
     (map value ∘ foldr _⊙↾_ [] ∘ filter (keyEq k) $ xs) ++
       (map (foldr _⊙_ z) ∘ filter (not ∘ null) ∘
         map (map value ∘ filter (keyEq k)) $ xss)
    ≡⟨ cong cxt₁ (foldr-↾-foldr k _⊙_ z xs k∈) ⟩
      map value ((k , foldr _⊙_ z (map value (filter (keyEq k) xs))) ∷ []) ++
       (map (foldr _⊙_ z) ∘ filter (not ∘ null) ∘
         map (map value ∘ filter (keyEq k)) $ xss)
    ≡⟨ refl ⟩
      foldr _⊙_ z (map value (filter (keyEq k) xs)) ∷
       (map (foldr _⊙_ z) ∘ filter (not ∘ null) ∘
         map (map value ∘ filter (keyEq k)) $ xss)
    ≡⟨ refl ⟩
      map (foldr _⊙_ z)
           (map value (filter (keyEq k) xs) ∷
             (filter (not ∘ null) ∘ map (map value ∘ filter (keyEq k)) $ xss))
    ≡⟨ cong (map (foldr _⊙_ z)) (sym (filter-¬null-filter-keyEq k xs k∈  _)) ⟩
     (map (foldr _⊙_ z) ∘
         filter (not ∘ null) $
          (map value (filter (keyEq k) xs) ∷
            map (map value ∘ filter (keyEq k)) xss))
    ≡⟨ refl ⟩
      (map (foldr _⊙_ z) ∘
                  filter (not ∘ null) ∘ map (map value ∘ filter (keyEq k))
                  $ xs ∷ xss)
    ≡∎
  branch (inj₂ k∉) =
    ≡-begin
     (map value ∘ foldr _⊙↾_ [] ∘ filter (keyEq k) $ xs) ++
       (map (foldr _⊙_ z) ∘ filter (not ∘ null) ∘
         map (map value ∘ filter (keyEq k)) $ xss)
    ≡⟨ cong cxt₁ (foldr-↾-foldr-¬∃ k _⊙_ z xs k∉) ⟩
     (map (foldr _⊙_ z) ∘ filter (not ∘ null) ∘
         map (map value ∘ filter (keyEq k)) $ xss)
    ≡⟨ cong (map (foldr _⊙_ z)) (sym (filter-keyEq-̸¬∃ k xs k∉ _)) ⟩
     (map (foldr _⊙_ z) ∘ filter (not ∘ null) $
         (map value (filter (keyEq k) xs) ∷
            map (map value ∘ filter (keyEq k)) xss))
    ≡⟨ refl ⟩
     (map (foldr _⊙_ z) ∘ filter (not ∘ null) ∘
         map (map value ∘ filter (keyEq k)) $ xs ∷ xss)
    ≡∎

-- naturalty laws we assume of perm
postulate
  map-perm : {A B : Set} (f : A → B)
           → map f ∘ perm ≗ perm ∘ map f
  filter-perm : {A : Set} (p : A → Bool)
              → filter p ∘ perm ≗ perm ∘ filter p

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


aggregateBy-aggregateWith :
  ∀ {A B} (k : Key) (z : B) (⊗ : A → B → B) (⊕ : B → B → B)
  → lookUp k z ∘ aggregateByKey z ⊗ ⊕ ≗ aggregateWithKey k z ⊗ ⊕
aggregateBy-aggregateWith k z ⊗ ⊕ xss =
  ≡-begin
   (lookUp k z ∘ aggregateByKey z ⊗ ⊕ $ xss)
  ≡⟨ refl ⟩
   (head' z ∘ concat ∘ map (map value ∘ filter (keyEq k)) ∘
      repartition ∘ foldr ↾⊕ [] ∘ concat ∘ map (foldr ↾⊗ []) ∘ perm $ xss)
  ≡⟨ cong (head' z) (naturalty₁ value (keyEq k) _) ⟩
   (head' z ∘ map value ∘ filter (keyEq k) ∘
     foldr ↾⊕ [] ∘ concat ∘ map (foldr ↾⊗ []) ∘ perm $ xss)
  ≡⟨ cong (head' z ∘ map value)
       (select-foldr k ⊕ z (concat ∘ map (foldr ↾⊗ []) ∘ perm $ xss)) ⟩
   (head' z ∘ map value ∘ foldr ↾⊕ [] ∘
     filter (keyEq k) ∘ concat ∘ map (foldr ↾⊗ []) ∘ perm $ xss)
  ≡⟨ head-foldr-↾ k z ⊕ (concat ∘ map (foldr ↾⊗ []) ∘ perm $ xss) ⟩
   (foldr ⊕ z ∘ map value ∘
      filter (keyEq k) ∘ concat ∘ map (foldr ↾⊗ []) ∘ perm $ xss)
  ≡⟨ cong (foldr ⊕ z) (naturalty₂ value (keyEq k) (foldr ↾⊗ []) (perm xss)) ⟩
   (foldr ⊕ z ∘ concat ∘
      map (map value ∘ filter (keyEq k) ∘ foldr ↾⊗ []) ∘ perm $ xss)
  ≡⟨ cong (foldr ⊕ z) (mapfold-select k z ⊗ (perm xss)) ⟩
   (foldr ⊕ z ∘ map (foldr ⊗ z) ∘
     filter (not ∘ null) ∘ map (map value ∘ filter (keyEq k)) ∘ perm $ xss)
  ≡⟨ cong (foldr ⊕ z ∘ map (foldr ⊗ z))
     (naturalty₃ (not ∘ null) _ xss) ⟩
   (foldr ⊕ z ∘ map (foldr ⊗ z) ∘ perm ∘
      filter (not ∘ null) ∘ map (map value ∘ filter (keyEq k)) $ xss)
  ≡⟨ refl ⟩
   aggregateWithKey k z ⊗ ⊕ xss
  ≡∎
 where
   ↾⊕ =  (↾ ⊕ z)
   ↾⊗ =  (↾ ⊗ z)

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

   naturalty₂ : {A B C : Set} (f : A → B) (p : A → Bool) (g : List C → List A) →
      map f ∘ filter p ∘ concat ∘ map g ≗
        concat ∘ map (map f ∘ filter p ∘ g)
   naturalty₂ f p g xss =
    ≡-begin
      (map f ∘ filter p ∘ concat ∘ map g $ xss)
    ≡⟨ cong (map f) (filter-concat p (map g xss)) ⟩
      (map f ∘ concat ∘ map (filter p) ∘ map g $ xss)
    ≡⟨ map-concat f (map (filter p) ∘ map g $ xss) ⟩
      (concat ∘ map (map f) ∘ map (filter p) ∘ map g $ xss)
    ≡⟨ cong (concat ∘ map (map f)) (map-map (filter p) g xss) ⟩
      (concat ∘ map (map f) ∘ map (filter p ∘ g) $ xss)
    ≡⟨ cong concat (map-map (map f) (filter p ∘ g) xss) ⟩
      (concat ∘ map (map f ∘ filter p ∘ g) $ xss)
    ≡∎

   naturalty₃ : {A B : Set} (p : B → Bool) (f : A → B) →
      filter p ∘ map f ∘ perm ≗ perm ∘ filter p ∘ map f
   naturalty₃ p f xs =
     ≡-begin
      (filter p ∘ map f ∘ perm $ xs)
     ≡⟨ cong (filter p) (map-perm f xs) ⟩
      (filter p ∘ perm ∘ map f $ xs)
     ≡⟨ filter-perm p _ ⟩
      (perm ∘ filter p ∘ map f $ xs)
     ≡∎
