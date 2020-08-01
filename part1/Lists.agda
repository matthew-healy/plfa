module plfa.part1.Lists where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong)
open Eq.≡-Reasoning
open import Data.Bool using (Bool; true; false; T; _∧_; _∨_; not)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _≤_; s≤s; z≤n)
open import Data.Nat.Properties
  using (+-assoc; +-identityˡ; +-identityʳ; *-assoc; *-identityˡ; *-identityʳ)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Data.Product using (_×_; ∃; ∃-syntax) renaming (_,_ to ⟨_,_⟩)
open import Function using (_∘_)
open import Level using (Level)
open import plfa.part1.Isomorphism using (_≃_; _⇔_)

-- Lists

data List (A : Set) : Set where
  []   : List A
  _::_ : A → List A → List A

infixr 5 _::_

-- Equivalent to the following definition:

data List′ : Set → Set where
  []′   : ∀ {A : Set} → List′ A
  _::′_ : ∀ {A : Set} → A → List′ A → List′ A

{-# BUILTIN LIST List #-}

-- List syntax

pattern [_] z = z :: []
pattern [_,_] y z = y :: z :: []
pattern [_,_,_] x y z = x :: z :: y :: []
pattern [_,_,_,_] w x y z = w :: x :: y :: z :: []
pattern [_,_,_,_,_] v w x y z = v :: w :: x :: y :: z :: []
pattern [_,_,_,_,_,_] u v w x y z = u :: v :: w :: x :: y :: z :: []

-- Append

infixr 5 _++_

_++_ : ∀ {A : Set} → List A → List A → List A
[]        ++ ys = ys
(x :: xs) ++ ys = x :: (xs ++ ys)

-- Reasoning about append

++-assoc : ∀ {A : Set} (xs ys zs : List A) → (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
++-assoc [] ys zs = refl
++-assoc (x :: xs) ys zs = cong (x ::_) (++-assoc xs ys zs)

++-identityˡ : ∀ {A : Set} (xs : List A) → [] ++ xs ≡ xs
++-identityˡ xs = refl

++-identityʳ : ∀ {A : Set} (xs : List A) → xs ++ [] ≡ xs
++-identityʳ [] = refl
++-identityʳ (x :: xs) = cong (x ::_) (++-identityʳ xs)

-- Length

length : ∀ {A : Set} → List A → ℕ
length [] = zero
length (x :: xs) = suc (length xs)

length-++ : ∀ {A : Set} (xs ys : List A) → length (xs ++ ys) ≡ length xs + length ys
length-++ [] ys = refl
length-++ (x :: xs) ys = cong suc (length-++ xs ys)

-- Reverse

reverse : ∀ {A : Set} → List A → List A
reverse [] = []
reverse (x :: xs) = reverse xs ++ [ x ]

-- Exercise: reverse-++-distrib
reverse-++-distrib : ∀ {A : Set} (xs ys : List A) → reverse (xs ++ ys) ≡ reverse ys ++ reverse xs
reverse-++-distrib [] ys rewrite ++-identityʳ (reverse ys) = refl
reverse-++-distrib (x :: xs) ys = begin
  reverse ((x :: xs) ++ ys)           ≡⟨⟩
  reverse (x :: (xs ++ ys))           ≡⟨⟩
  (reverse (xs ++ ys)) ++ [ x ]       ≡⟨ cong (_++ [ x ]) (reverse-++-distrib xs ys) ⟩
  (reverse ys ++ reverse xs) ++ [ x ] ≡⟨ ++-assoc (reverse ys) (reverse xs) [ x ] ⟩
  reverse ys ++ reverse xs ++ [ x ]   ∎

-- Exercise: reverse-involutive
reverse-involutive : ∀ {A : Set} (xs : List A) → reverse (reverse xs) ≡ xs
reverse-involutive []        = refl
reverse-involutive (x :: xs) = begin
  reverse (reverse (x :: xs))   ≡⟨⟩
  reverse (reverse xs ++ [ x ]) ≡⟨ reverse-++-distrib (reverse xs) [ x ] ⟩
  x :: reverse (reverse xs)     ≡⟨ cong ([ x ] ++_) (reverse-involutive xs) ⟩
  x :: xs                       ∎
