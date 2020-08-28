module plfa.part2.More where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (ℕ; zero; suc; _*_)
open import Relation.Nullary using (¬_)

-- Syntax
infix  4 _⊢_
infix  4 _∋_
infixl 5 _,_

infixr 7 _⇒_
infixr 9 _`×_

infix  5 ƛ_
infix  5 μ_
infixl 7 _·_
infixl 8 _`*_
infix  8 `suc_
infix  9 `_
infix  9 S_
infix  9 #_

-- Types
data Type : Set where
  `ℕ   : Type
  _⇒_  : Type → Type → Type
  Nat  : Type
  _`×_ : Type → Type → Type

-- Contexts
data Context : Set where
  ∅   : Context
  _,_ : Context → Type → Context

-- Variables and the lookup judgement
data _∋_ : Context → Type → Set where
  Z : ∀ {Γ A}
      ---------
    → Γ , A ∋ A

  S_ : ∀ {Γ A B}
    → Γ ∋ B
      ---------
    → Γ , A ∋ B

data _⊢_ : Context → Type → Set where

  -- variables
  `_ : ∀ {Γ A}
    → Γ ∋ A
      -----
    → Γ ⊢ A

  -- functions

  ƛ_ : ∀ {Γ A B}
    → Γ , A ⊢ B
      ---------
    → Γ ⊢ A ⇒ B

  _·_ : ∀ {Γ A B}
    → Γ ⊢ A ⇒ B
    → Γ ⊢ A
      ---------
    → Γ ⊢ B

  -- naturals

  `zero : ∀ {Γ}
      ------
    → Γ ⊢ `ℕ

  `suc_ : ∀ {Γ}
    → Γ ⊢ `ℕ
      ------
    → Γ ⊢ `ℕ

  case : ∀ {Γ A}
    → Γ ⊢ `ℕ
    → Γ ⊢ A
    → Γ , `ℕ ⊢ A
      ----------
    → Γ ⊢ A

  -- fixpoint

  μ_ : ∀ {Γ A}
    → Γ , A ⊢ A
      ---------
    → Γ ⊢ A

  -- primitive numbers

  con : ∀ {Γ}
    → ℕ
      -------
    → Γ ⊢ Nat

  _`*_ : ∀ {Γ}
    → Γ ⊢ Nat
    → Γ ⊢ Nat
      -------
    → Γ ⊢ Nat

  -- let
  `let : ∀ {Γ A B}
    → Γ ⊢ A
    → Γ , A ⊢ B
      ---------
    → Γ ⊢ B

  -- products

  `⟨_,_⟩ : ∀ {Γ A B}
    → Γ ⊢ A
    → Γ ⊢ B
      ------
    → Γ ⊢ A `× B

  `proj₁ : ∀ {Γ A B}
    → Γ ⊢ A `× B
      ----------
    → Γ ⊢ A

  `proj₂ : ∀ {Γ A B}
    → Γ ⊢ A `× B
      ----------
    → Γ ⊢ B

  -- alternative formulation of products

  casex : ∀ {Γ A B C}
    → Γ ⊢ A `× B
    → Γ , A , B ⊢ C
      -------------
    → Γ ⊢ C

-- Abbreviating de Bruijn indices

lookup : Context → ℕ → Type
lookup (Γ , A) zero    = A
lookup (Γ , _) (suc n) = lookup Γ n
lookup ∅       _       = ⊥-elim impossible
  where postulate impossible : ⊥

count : ∀ {Γ} → (n : ℕ) → Γ ∋ lookup Γ n
count {Γ , _} zero    = Z
count {Γ , _} (suc n) = S (count n)
count {∅}     _       = ⊥-elim impossible
  where postulate impossible : ⊥

#_ : ∀ {Γ} → (n : ℕ) → Γ ⊢ lookup Γ n
# n = ` count n
