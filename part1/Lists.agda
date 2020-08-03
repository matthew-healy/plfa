module plfa.part1.Lists where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong)
open Eq.≡-Reasoning
open import Data.Bool using (Bool; true; false; T; _∧_; _∨_; not)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _≤_; s≤s; z≤n)
open import Data.Nat.Properties
  using (+-assoc; +-identityˡ; +-identityʳ; *-assoc; *-identityˡ; *-identityʳ; *-comm)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Data.Empty using (⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; proj₁; proj₂; ∃; ∃-syntax) renaming (_,_ to ⟨_,_⟩)
open import Function using (_∘_)
open import Level using (Level)
open import plfa.part1.Isomorphism using (_≃_; _⇔_; extensionality)

-- Lists

data List (A : Set) : Set where
  []   : List A
  _∷_ : A → List A → List A

infixr 5 _∷_

-- Equivalent to the following definition:

data List′ : Set → Set where
  []′   : ∀ {A : Set} → List′ A
  _∷′_ : ∀ {A : Set} → A → List′ A → List′ A

{-# BUILTIN LIST List #-}

-- List syntax

pattern [_] z = z ∷ []
pattern [_,_] y z = y ∷ z ∷ []
pattern [_,_,_] x y z = x ∷ y ∷ z ∷ []
pattern [_,_,_,_] w x y z = w ∷ x ∷ y ∷ z ∷ []
pattern [_,_,_,_,_] v w x y z = v ∷ w ∷ x ∷ y ∷ z ∷ []
pattern [_,_,_,_,_,_] u v w x y z = u ∷ v ∷ w ∷ x ∷ y ∷ z ∷ []

-- Append

infixr 5 _++_

_++_ : ∀ {A : Set} → List A → List A → List A
[]        ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

-- Reasoning about append

++-assoc : ∀ {A : Set} (xs ys zs : List A) → (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
++-assoc [] ys zs = refl
++-assoc (x ∷ xs) ys zs = cong (x ∷_) (++-assoc xs ys zs)

++-identityˡ : ∀ {A : Set} (xs : List A) → [] ++ xs ≡ xs
++-identityˡ xs = refl

++-identityʳ : ∀ {A : Set} (xs : List A) → xs ++ [] ≡ xs
++-identityʳ [] = refl
++-identityʳ (x ∷ xs) = cong (x ∷_) (++-identityʳ xs)

-- Length

length : ∀ {A : Set} → List A → ℕ
length [] = zero
length (x ∷ xs) = suc (length xs)

length-++ : ∀ {A : Set} (xs ys : List A) → length (xs ++ ys) ≡ length xs + length ys
length-++ [] ys = refl
length-++ (x ∷ xs) ys = cong suc (length-++ xs ys)

-- Reverse

reverse : ∀ {A : Set} → List A → List A
reverse [] = []
reverse (x ∷ xs) = reverse xs ++ [ x ]

-- Exercise: reverse-++-distrib
reverse-++-distrib : ∀ {A : Set} (xs ys : List A) → reverse (xs ++ ys) ≡ reverse ys ++ reverse xs
reverse-++-distrib [] ys rewrite ++-identityʳ (reverse ys) = refl
reverse-++-distrib (x ∷ xs) ys = begin
  reverse ((x ∷ xs) ++ ys)            ≡⟨⟩
  reverse (x ∷ (xs ++ ys))            ≡⟨⟩
  (reverse (xs ++ ys)) ++ [ x ]       ≡⟨ cong (_++ [ x ]) (reverse-++-distrib xs ys) ⟩
  (reverse ys ++ reverse xs) ++ [ x ] ≡⟨ ++-assoc (reverse ys) (reverse xs) [ x ] ⟩
  reverse ys ++ reverse xs ++ [ x ]   ∎

-- Exercise: reverse-involutive
reverse-involutive : ∀ {A : Set} (xs : List A) → reverse (reverse xs) ≡ xs
reverse-involutive []        = refl
reverse-involutive (x ∷ xs) = begin
  reverse (reverse (x ∷ xs))    ≡⟨⟩
  reverse (reverse xs ++ [ x ]) ≡⟨ reverse-++-distrib (reverse xs) [ x ] ⟩
  x ∷ reverse (reverse xs)      ≡⟨ cong ([ x ] ++_) (reverse-involutive xs) ⟩
  x ∷ xs                        ∎

-- Faster Reverse

shunt : ∀ {A : Set} → List A → List A → List A
shunt []        ys = ys
shunt (x ∷ xs) ys = shunt xs (x ∷ ys)

shunt-reverse : ∀ {A : Set} (xs ys : List A) → shunt xs ys ≡ reverse xs ++ ys
shunt-reverse [] ys = refl
shunt-reverse (x ∷ xs) ys = begin
  shunt (x ∷ xs) ys           ≡⟨⟩
  shunt xs (x ∷ ys)           ≡⟨ shunt-reverse xs (x ∷ ys) ⟩
  reverse xs ++ (x ∷ ys)      ≡⟨⟩
  reverse xs ++ ([ x ] ++ ys) ≡⟨ sym (++-assoc (reverse xs) [ x ] ys) ⟩
  (reverse xs ++ [ x ]) ++ ys ≡⟨⟩
  reverse (x ∷ xs) ++ ys      ∎

reverse′ : ∀ {A : Set} → List A → List A
reverse′ xs = shunt xs []


reverses : ∀ {A : Set} (xs : List A) → reverse′ xs ≡ reverse xs
reverses xs = begin
  reverse′ xs      ≡⟨⟩
  shunt xs []      ≡⟨ shunt-reverse xs [] ⟩
  reverse xs ++ [] ≡⟨ ++-identityʳ (reverse xs) ⟩
  reverse xs       ∎

-- Map

map : ∀ {A B : Set} → (A → B) → List A → List B
map f [] = []
map f (x ∷ xs) = f x ∷ map f xs

-- Exercise: map-compose
map-compose-xs : ∀ {A B C : Set} (f : A → B) (g : B → C) (xs : List A) → map (g ∘ f) xs ≡ (map g ∘ map f) xs
map-compose-xs f g [] = refl
map-compose-xs f g (x ∷ xs) = cong (g (f x) ∷_) (map-compose-xs f g xs)

map-compose : ∀ {A B C : Set} (f : A → B) (g : B → C) → map (g ∘ f) ≡ map g ∘ map f
map-compose f g = extensionality λ{ xs → map-compose-xs f g xs }

-- Exercise: map-++-distribute
map-++-distribute : ∀ {A B : Set} (f : A → B) (xs ys : List A) → map f (xs ++ ys) ≡ map f xs ++ map f ys
map-++-distribute f [] ys = refl
map-++-distribute f (x ∷ xs) ys = cong (f x ∷_) (map-++-distribute f xs ys)

-- Exercise: map-tree
data Tree (A B : Set) : Set where
  leaf : A → Tree A B
  node : Tree A B → B → Tree A B → Tree A B

map-Tree : ∀ {A B C D : Set} → (A → C) → (B → D) → Tree A B → Tree C D
map-Tree f g (leaf x)     = leaf (f x)
map-Tree f g (node l x r) = node (map-Tree f g l) (g x) (map-Tree f g r)

-- Fold

foldr : ∀ {A B : Set} → (A → B → B) → B → List A → B
foldr _⊗_ e [] = e
foldr _⊗_ e (x ∷ xs) = x ⊗ (foldr _⊗_ e xs)

foldr-∷-[] : ∀ {A : Set} (xs : List A) → foldr _∷_ [] xs ≡ xs
foldr-∷-[] [] = refl
foldr-∷-[] (x ∷ xs) = cong (x ∷_) (foldr-∷-[] xs)

foldr-∷-ys : ∀ {A : Set} (xs ys : List A) → xs ++ ys ≡ foldr _∷_ ys xs
foldr-∷-ys [] ys = refl
foldr-∷-ys (x ∷ xs) ys = cong (x ∷_) (foldr-∷-ys xs ys)

-- Exercise: product
product : List ℕ → ℕ
product = foldr _*_ 1

-- Exercise: foldr-++
foldr-++ : ∀ {A B : Set} {_⊗_ : A → B → B} {e : B} (xs ys : List A)
  → (foldr _⊗_ e (xs ++ ys)) ≡ (foldr _⊗_ (foldr _⊗_ e ys) xs)
foldr-++             []       ys = refl
foldr-++ {_⊗_ = _⊗_} (x ∷ xs) ys = cong (x ⊗_) (foldr-++ xs ys)

-- Exercise: foldr-∷
foldr-∷ : ∀ {A : Set} (xs : List A) → foldr _∷_ [] xs ≡ xs
foldr-∷ []       = refl
foldr-∷ (x ∷ xs) = cong (x ∷_) (foldr-∷ xs)

foldr-++-consequence : ∀ {A : Set} (xs ys : List A) → xs ++ ys ≡ foldr _∷_ ys xs
foldr-++-consequence [] ys = refl
foldr-++-consequence (x ∷ xs) ys = cong (x ∷_) (foldr-++-consequence xs ys)

-- Exercise: map-is-foldr
map-is-foldr-xs : ∀ {A B : Set} (f : A → B) (xs : List A) → map f xs ≡ foldr (λ y ys → f y ∷ ys) [] xs
map-is-foldr-xs f [] = refl
map-is-foldr-xs f (x ∷ xs) = cong (f x ∷_) (map-is-foldr-xs f xs)

map-is-foldr : ∀ {A B : Set} (f : A → B) → map f ≡ foldr (λ x xs → f x ∷ xs) []
map-is-foldr f = extensionality λ{ xs → map-is-foldr-xs f xs}


-- Exercise: fold-Tree
fold-Tree : ∀ {A B C : Set} → (A → C) → (C → B → C → C) → Tree A B → C
fold-Tree f g (leaf x)             = f x
fold-Tree f g (node ltree y rtree) = g (fold-Tree f g ltree) y (fold-Tree f g rtree)

-- Exercise: map-is-fold-Tree
fold-map : ∀ {A B C D : Set} → (A → C) → (B → D) → Tree A B → Tree C D
fold-map f g t = fold-Tree (λ x → leaf (f x)) (λ l y r → node l (g y) r) t

map-is-fold-Tree-t : ∀ {A B C D : Set} (f : A → C) (g : B → D) (t : Tree A B) -- ret type is Tree C D
  → map-Tree f g t ≡ fold-map f g t
map-is-fold-Tree-t f g (leaf x)      = refl
map-is-fold-Tree-t f g (node l y r) = begin
  map-Tree f g (node l y r)                    ≡⟨⟩
  node (map-Tree f g l) (g y) (map-Tree f g r) ≡⟨ cong (λ x → node x (g y) (map-Tree f g r)) (map-is-fold-Tree-t f g l) ⟩
  node (fold-map f g l) (g y) (map-Tree f g r) ≡⟨ cong (λ x → node (fold-map f g l) (g y) x) (map-is-fold-Tree-t f g r) ⟩
  node (fold-map f g l) (g y) (fold-map f g r) ≡⟨⟩
  fold-map f g (node l y r)                    ∎

-- Exercise: sum-downFrom
sum : List ℕ → ℕ
sum = foldr _+_ 0

downFrom : ℕ → List ℕ
downFrom zero    = []
downFrom (suc n) = n ∷ downFrom n

n*[2+[n∸1]]≡n*sn : ∀ (n : ℕ) → n * (2 + (n ∸ 1)) ≡ n * suc n
n*[2+[n∸1]]≡n*sn zero    = refl
n*[2+[n∸1]]≡n*sn (suc n) = refl

-- *-distrib-+ in stdlib is causing some issues here.
*-distrib-+ : ∀ (m n p : ℕ) → (m + n) * p ≡ m * p + n * p
*-distrib-+ zero n p = refl
*-distrib-+ (suc m) n p rewrite *-distrib-+ m n p | sym (+-assoc p (m * p) (n * p)) = refl

n*0≡0 : ∀ (n : ℕ) → n * 0 ≡ 0
n*0≡0 zero    = refl
n*0≡0 (suc n) = n*0≡0 n

+-factor-* : ∀ (m n p : ℕ) → p * m + p * n ≡ p * (m + n)
+-factor-* m n p = begin
  p * m + p * n ≡⟨ cong (_+ p * n) (*-comm p m) ⟩
  m * p + p * n ≡⟨ cong (m * p +_) (*-comm p n) ⟩
  m * p + n * p ≡⟨ sym (*-distrib-+ m n p) ⟩
  (m + n) * p   ≡⟨ *-comm (m + n) p ⟩
  p * (m + n)   ∎

sum-downFrom : ∀ (n : ℕ) → sum (downFrom n) * 2 ≡ n * (n ∸ 1)
sum-downFrom zero    = refl
sum-downFrom (suc n) = begin
  sum (n ∷ downFrom n) * 2     ≡⟨⟩
  (n + sum (downFrom n)) * 2   ≡⟨ *-distrib-+ n (sum (downFrom n)) 2 ⟩
  n * 2 + sum (downFrom n) * 2 ≡⟨ cong (n * 2 +_) (sum-downFrom n) ⟩
  n * 2 + n * (n ∸ 1)          ≡⟨ +-factor-* 2 (n ∸ 1) n ⟩
  n * (2 + (n ∸ 1))            ≡⟨ n*[2+[n∸1]]≡n*sn n ⟩
  n * suc n                    ≡⟨ *-comm n (suc n) ⟩
  suc n * n                    ≡⟨⟩
  suc n * (suc n ∸ 1)          ∎

-- Monoids

record IsMonoid {A : Set} (_⊗_ : A → A → A) (e : A) : Set where
  field
    assoc     : ∀ (x y z : A) → (x ⊗ y) ⊗ z ≡ x ⊗ (y ⊗ z)
    identityˡ : ∀ (x : A) → e ⊗ x ≡ x
    identityʳ : ∀ (x : A) → x ⊗ e ≡ x

open IsMonoid

+-monoid : IsMonoid _+_ 0
+-monoid = record
  { assoc     = +-assoc
  ; identityˡ = +-identityˡ
  ; identityʳ = +-identityʳ
  }

*-monoid : IsMonoid _*_ 1
*-monoid = record
  { assoc     = *-assoc
  ; identityˡ = *-identityˡ
  ; identityʳ = *-identityʳ
  }

++-monoid : ∀ {A : Set} → IsMonoid {List A} _++_ []
++-monoid = record
  { assoc     = ++-assoc
  ; identityˡ = ++-identityˡ
  ; identityʳ = ++-identityʳ
  }

-- e.g. foldr _+_ 3 [ 1 , 2 ] = 6 = 3 + 3 = (foldr _+_ 0 [ 1 , 2 ]) + 3
foldr-monoid : ∀ {A : Set} (_⊗_ : A → A → A) (e : A) → IsMonoid _⊗_ e →
  ∀ (xs : List A) (y : A) → foldr _⊗_ y xs ≡ (foldr _⊗_ e xs) ⊗ y

foldr-monoid _⊗_ e ⊗-monoid [] y       = begin
  foldr _⊗_ y []       ≡⟨⟩
  y                    ≡⟨ sym (identityˡ ⊗-monoid y) ⟩
  e ⊗ y                ≡⟨⟩
  (foldr _⊗_ e []) ⊗ y ∎

foldr-monoid _⊗_ e ⊗-monoid (x ∷ xs) y = begin
  foldr _⊗_ y (x ∷ xs)       ≡⟨⟩
  x ⊗ (foldr _⊗_ y xs)       ≡⟨ cong (x ⊗_) (foldr-monoid _⊗_ e ⊗-monoid xs y) ⟩
  x ⊗ ((foldr _⊗_ e xs) ⊗ y) ≡⟨ sym (assoc ⊗-monoid x (foldr _⊗_ e xs) y) ⟩
  (x ⊗ (foldr _⊗_ e xs)) ⊗ y ≡⟨⟩
  (foldr _⊗_ e (x ∷ xs)) ⊗ y ∎

-- As a consequence of foldr-monoid and foldr-++
foldr-monoid-++ : ∀ {A : Set} (_⊗_ : A → A → A) (e : A) → IsMonoid _⊗_ e →
  ∀ (xs ys : List A) → foldr _⊗_ e (xs ++ ys) ≡ foldr _⊗_ e xs ⊗ (foldr _⊗_ e ys)
foldr-monoid-++ _⊗_ e ⊗-monoid xs ys rewrite foldr-++ {_⊗_ = _⊗_} {e = e} xs ys = foldr-monoid _⊗_ e ⊗-monoid xs (foldr _⊗_ e ys)

-- Exercise: foldl
foldl : ∀ {A B : Set} → (B → A → B) → B → List A → B
foldl _⊗_ e []       = e
foldl _⊗_ e (x ∷ xs) = foldl _⊗_ (e ⊗ x) xs

-- Exercise: foldr-monoid-foldl
foldl-monoid : ∀ {A : Set} (_⊗_ : A → A → A) (e : A)
  → IsMonoid _⊗_ e
    ---------------------------------------------------------------
  → ∀ (xs : List A) (y : A) → y ⊗ (foldl _⊗_ e xs) ≡ foldl _⊗_ y xs
foldl-monoid _⊗_ e ⊗-monoid [] y       = identityʳ ⊗-monoid y
foldl-monoid _⊗_ e ⊗-monoid (x ∷ xs) y = begin
  y ⊗ (foldl _⊗_ e (x ∷ xs)) ≡⟨⟩
  y ⊗ (foldl _⊗_ (e ⊗ x) xs) ≡⟨ cong (λ x → y ⊗ (foldl _⊗_ x xs)) (identityˡ ⊗-monoid x) ⟩
  y ⊗ (foldl _⊗_ x xs)       ≡⟨ cong (y ⊗_) (sym (foldl-monoid _⊗_ e ⊗-monoid xs x)) ⟩
  y ⊗ (x ⊗ foldl _⊗_ e xs)   ≡⟨ sym (assoc ⊗-monoid y x (foldl _⊗_ e xs)) ⟩
  (y ⊗ x) ⊗ (foldl _⊗_ e xs) ≡⟨ foldl-monoid _⊗_ e ⊗-monoid xs (y ⊗ x) ⟩
  foldl _⊗_ (y ⊗ x) xs       ≡⟨⟩
  foldl _⊗_ y (x ∷ xs)       ∎

foldr-monoid-foldl : ∀ {A : Set} (_⊗_ : A → A → A) (e : A)
  → IsMonoid _⊗_ e
    -------------------------
  → foldr _⊗_ e ≡ foldl _⊗_ e
foldr-monoid-foldl _⊗_ e ⊗-monoid = extensionality (foldr-monoid-foldl-xs _⊗_ e ⊗-monoid) where
  foldr-monoid-foldl-xs : ∀ {A : Set} (_⊗_ : A → A → A) (e : A)
    → IsMonoid _⊗_ e
    ---------------------------------------------------
    → ∀ (xs : List A) → foldr _⊗_ e xs ≡ foldl _⊗_ e xs
  foldr-monoid-foldl-xs _⊗_ e ⊗-monoid []       = refl
  foldr-monoid-foldl-xs _⊗_ e ⊗-monoid (x ∷ xs) = begin
    foldr _⊗_ e (x ∷ xs) ≡⟨⟩
    x ⊗ foldr _⊗_ e xs   ≡⟨ cong (x ⊗_) (foldr-monoid-foldl-xs _⊗_ e ⊗-monoid xs) ⟩
    x ⊗ foldl _⊗_ e xs   ≡⟨ foldl-monoid _⊗_ e ⊗-monoid xs x ⟩
    foldl _⊗_ x xs       ≡⟨ cong (λ x → foldl _⊗_ x xs) (sym (identityˡ ⊗-monoid x) ) ⟩
    foldl _⊗_ (e ⊗ x) xs ≡⟨⟩
    foldl _⊗_ e (x ∷ xs) ∎

-- All

data All {A : Set} (P : A → Set) : List A → Set where
  []  : All P []
  _∷_ : ∀ {x : A} {xs : List A} → P x → All P xs → All P (x ∷ xs)

_ : All (_≤ 2) [ 0 , 1 , 2 ]
_ = z≤n ∷ s≤s z≤n ∷ s≤s (s≤s z≤n) ∷ []

-- Any

data Any {A : Set} (P : A → Set) : List A → Set where
  here  : ∀ {x : A} {xs : List A} → P x → Any P (x ∷ xs)
  there : ∀ {x : A} {xs : List A} → Any P xs → Any P (x ∷ xs)

infix 4 _∈_ _∉_

_∈_ : ∀ {A : Set} (x : A) (xs : List A) → Set
x ∈ xs = Any (x ≡_) xs

_∉_ : ∀ {A : Set} (x : A) (xs : List A) → Set
x ∉ xs = ¬ (x ∈ xs)

_ : 0 ∈ [ 0 , 1 , 0 , 2 ]
_ = here refl

_ : 0 ∈ [ 0 , 1 , 0 , 2 ]
_ = there (there (here refl))

not-in : 3 ∉ [ 0 , 1 , 0 , 2 ]
not-in (there (there (there (here ()))))
not-in (there (there (there (there ()))))

-- All and append

All-++-to : ∀ {A : Set} {P : A → Set} (xs ys : List A) →
  All P (xs ++ ys) → (All P xs × All P ys)
All-++-to []       ys Pys        = ⟨ [] , Pys ⟩
All-++-to (x ∷ xs) ys (Px ∷ Pxs++ys) with All-++-to xs ys Pxs++ys
...                          | ⟨ Pxs , Pys ⟩ = ⟨ Px ∷ Pxs , Pys ⟩

All-++-from : ∀ {A : Set} {P : A → Set} (xs ys : List A) →
  All P xs × All P ys → All P (xs ++ ys)
All-++-from []       ys ⟨ [] , Pys ⟩       = Pys
All-++-from (x ∷ xs) ys ⟨ Px ∷ Pxs , Pys ⟩ = Px ∷ (All-++-from xs ys ⟨ Pxs , Pys ⟩)

All-++-⇔ : ∀ {A : Set} {P : A → Set} (xs ys : List A) →
  All P (xs ++ ys) ⇔ (All P xs × All P ys)
All-++-⇔ xs ys = record
  { to   = All-++-to xs ys
  ; from = All-++-from xs ys
  }

-- Exercise: Any-++-⇔
Any-++-⇔ : ∀ {A : Set} {P : A → Set} (xs ys : List A) →
  Any P (xs ++ ys) ⇔ (Any P xs ⊎ Any P ys)
Any-++-⇔ xs ys = record
  { to   = to xs ys
  ; from = from xs ys
  }
  where

  to : ∀ {A : Set} {P : A → Set} (xs ys : List A) →
    Any P (xs ++ ys) → (Any P xs ⊎ Any P ys)
  to []       ys Pxs++ys   = inj₂ Pxs++ys
  to (x ∷ xs) ys (here Px) = inj₁ (here Px)
  to (x ∷ xs) ys (there Pxs++ys) with to xs ys Pxs++ys
  ...                                | inj₁ Pxs = inj₁ (there Pxs)
  ...                                | inj₂ Pys = inj₂ Pys

  from : ∀ {A : Set} {P : A → Set} (xs ys : List A) →
    (Any P xs ⊎ Any P ys) → Any P (xs ++ ys)
  from [] ys (inj₂ Py) = Py
  from (x ∷ xs) ys (inj₁ (here Px)) = here Px
  from (x ∷ xs) ys (inj₁ (there Pxs)) = there (from xs ys (inj₁ Pxs))
  from (x ∷ xs) ys (inj₂ Pys) = there (from xs ys (inj₂ Pys))

-- Exercise: All-++-≃
All-++-from∘to : ∀ {A : Set} {P : A → Set} (xs ys : List A) (p : All P (xs ++ ys)) →
  All-++-from xs ys (All-++-to xs ys p) ≡ p
All-++-from∘to [] ys p = refl
All-++-from∘to (x ∷ xs) ys (Px ∷ Pxs++ys) = cong (Px ∷_) (All-++-from∘to xs ys Pxs++ys)

All-++-to∘from : ∀ {A : Set} {P : A → Set} (xs ys : List A) (p : All P xs × All P ys) →
  All-++-to xs ys (All-++-from xs ys p) ≡ p
All-++-to∘from [] ys ⟨ [] , Pys ⟩ = refl
All-++-to∘from (x ∷ xs) ys ⟨ Px ∷ Pxs , Pys ⟩ =
  begin
    to (x ∷ xs) ys (from (x ∷ xs) ys ⟨ Px ∷ Pxs , Pys ⟩)
  ≡⟨⟩
    to (x ∷ xs) ys (Px ∷ (from xs ys ⟨ Pxs , Pys ⟩))
  ≡⟨⟩
    ⟨ Px ∷ (proj₁ (to xs ys (from xs ys ⟨ Pxs , Pys ⟩))) , proj₂ (to xs ys (from xs ys ⟨ Pxs , Pys ⟩)) ⟩
  ≡⟨ cong (λ{ x → ⟨ Px ∷ (proj₁ x) , proj₂ (to xs ys (from xs ys ⟨ Pxs , Pys ⟩)) ⟩ }) (All-++-to∘from xs ys ⟨ Pxs , Pys ⟩) ⟩
    ⟨ Px ∷ Pxs , proj₂ (to xs ys (from xs ys ⟨ Pxs , Pys ⟩)) ⟩
  ≡⟨ cong (λ{ x → ⟨ Px ∷ Pxs , proj₂ x ⟩ }) (All-++-to∘from xs ys ⟨ Pxs , Pys ⟩) ⟩
    ⟨ Px ∷ Pxs , Pys ⟩ ∎
  where
    to = All-++-to
    from = All-++-from

All-++-≃ : ∀ {A : Set} {P : A → Set} (xs ys : List A) →
  All P (xs ++ ys) ≃ (All P xs × All P ys)
All-++-≃ xs ys = record
  { to      = All-++-to xs ys
  ; from    = All-++-from xs ys
  ; from∘to = All-++-from∘to xs ys
  ; to∘from = All-++-to∘from xs ys
  }

-- Exercise: ¬Any⇔All¬
¬Any⇔All¬ : ∀ {A : Set} {P : A → Set} (xs : List A) → (¬_ ∘ Any P) xs ⇔ All (¬_ ∘ P) xs
¬Any⇔All¬ xs = record
  { to   = to xs
  ; from = from xs
  }
  where

    to : ∀ {A : Set} {P : A → Set} (xs : List A) → (¬_ ∘ Any P) xs → All (¬_ ∘ P) xs
    to [] ¬AnyP       = []
    to (x ∷ xs) ¬AnyP = (λ Px → ¬AnyP (here Px) ) ∷ to xs (λ Pxs → ¬AnyP (there Pxs))

    from : ∀ {A : Set} {P : A → Set} (xs : List A) → All (¬_ ∘ P) xs → (¬_ ∘ Any P) xs
    from [] All¬P ()
    from (x ∷ xs) (¬Px ∷ All¬P) (here Px) = ¬Px Px
    from (x ∷ xs) (¬Px ∷ All¬P) (there Pxs) = from xs All¬P Pxs

-- Why is it important that _∘_ is generalised to arbitrary levels?

-- Do we also have (¬_ ∘ All P) xs ⇔ Any (¬_ ∘ P) xs
-- No, this does not hold. We know that not all xs satisfy P, but we cannot
-- provide evidence that any specific x ∈ xs satisfies ¬P.
-- We can however show that Any (¬_ ∘ P) xs → (¬_ ∘ All P) xs

-- Exercise: ¬Any≃All¬
¬Any≃All¬ : ∀ {A : Set} {P : A → Set} (xs : List A) → (¬_ ∘ Any P) xs ≃ All (¬_ ∘ P) xs
¬Any≃All¬ xs = record
  { to      = to xs
  ; from    = from xs
  ; from∘to = from∘to xs
  ; to∘from = to∘from xs
  }
  where

    to : ∀ {A : Set} {P : A → Set} (xs : List A) → (¬_ ∘ Any P) xs → All (¬_ ∘ P) xs
    to [] ¬AnyP       = []
    to (x ∷ xs) ¬AnyP = (λ Px → ¬AnyP (here Px)) ∷ to xs (λ Pxs → ¬AnyP (there Pxs))

    from : ∀ {A : Set} {P : A → Set} (xs : List A) → All (¬_ ∘ P) xs → (¬_ ∘ Any P) xs
    from [] All¬P ()
    from (x ∷ xs) (¬Px ∷ All¬P) (here Px) = ¬Px Px
    from (x ∷ xs) (¬Px ∷ All¬P) (there Pxs) = from xs All¬P Pxs

    from∘to : ∀ {A : Set} {P : A → Set} (xs : List A) (p : (¬_ ∘ Any P) xs) → from xs (to xs p) ≡ p
    from∘to [] ¬AnyP = extensionality λ ()
    from∘to (x ∷ xs) ¬AnyP = extensionality λ{ (here Px) → refl
                                             ; (there Pxs) → ⊥-elim (¬AnyP (there Pxs))
                                             }

    to∘from : ∀ {A : Set} {P : A → Set} (xs : List A) (p : All (¬_ ∘ P) xs) → to xs (from xs p) ≡ p
    to∘from [] []      = refl
    to∘from (x ∷ xs) (Px ∷ Pxs) = cong (Px ∷_) (to∘from xs Pxs)
