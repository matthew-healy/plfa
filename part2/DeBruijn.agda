module plfa.part2.DeBruijn where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (ℕ; zero; suc)
open import Relation.Nullary using (¬_)

-- Syntax

infix  4 _⊢_
infix  4 _∋_
infixl 5 _,_

infixr 7 _⇒_

infix  5 ƛ_
infix  5 μ_
infixl 7 _·_
infix  8 `suc_
infix  9 `_
infix  9 S_
infix  9 #_

-- Types

data Type : Set where
  _⇒_ : Type → Type → Type
  `ℕ  : Type

-- Contexts

data Context : Set where
  ∅   : Context
  _,_ : Context → Type → Context

_ : Context
_ = ∅ , `ℕ ⇒ `ℕ , `ℕ

-- Variables and the lookup judgement

data _∋_ : Context → Type → Set where
  Z : ∀ {Γ A}
      ---------
    → Γ , A ∋ A

  S_ : ∀ {Γ A B}
    → Γ ∋ A
      ---------
    → Γ , B ∋ A

-- Previously: ∅ , "s" ⦂ `ℕ ⇒ `ℕ , "z" ⦂ `ℕ ∋ "z" ⦂ `ℕ
_ : ∅ , `ℕ ⇒ `ℕ , `ℕ ∋ `ℕ
_ = Z

-- Previously: ∅ , "s" ⦂ `ℕ ⇒ `ℕ , "z" ⦂ `ℕ ∋ "s" ⦂ `ℕ ⇒ `ℕ
_ : ∅ , `ℕ ⇒ `ℕ , `ℕ ∋ `ℕ ⇒ `ℕ
_ = S Z

-- Terms and the typing judgement

data _⊢_ : Context → Type → Set where
  `_ : ∀ {Γ A}
    → Γ ∋ A
      -----
    → Γ ⊢ A

  ƛ_ : ∀ {Γ A B}
    → Γ , A ⊢ B
      ---------
    → Γ ⊢ A ⇒ B

  _·_ : ∀ {Γ A B}
    → Γ ⊢ A ⇒ B
    → Γ ⊢ A
      ---------
    → Γ ⊢ B

  `zero : ∀ {Γ}
      -------
    → Γ ⊢ `ℕ

  `suc_ : ∀ {Γ}
    → Γ ⊢ `ℕ
      -------
    → Γ ⊢ `ℕ

  case : ∀ {Γ A}
    → Γ ⊢ `ℕ
    → Γ ⊢ A
    → Γ , `ℕ ⊢ A
      ----------
    → Γ ⊢ A

  μ_ : ∀ {Γ A}
    → Γ , A ⊢ A
      ---------
    → Γ ⊢ A

-- Previously: ∅ , "s" ⦂ `ℕ ⇒ `ℕ , "z" ⦂ `ℕ ⊢ ` "z" ⦂ `ℕ
_ : ∅ , `ℕ ⇒ `ℕ , `ℕ ⊢ `ℕ
_ = ` Z

-- Previously: ∅ , "s" ⦂ `ℕ ⇒ `ℕ , "z" ⦂ `ℕ ⊢ ` "s" ⦂ `ℕ ⇒ `ℕ
_ : ∅ , `ℕ ⇒ `ℕ , `ℕ ⊢ `ℕ ⇒ `ℕ
_ = ` S Z

-- Previously: ∅ , "s" ⦂ `ℕ ⇒ `ℕ , "z" ⦂ `ℕ ⊢ ` "s" · ` "z" ⦂  `ℕ
_ : ∅ , `ℕ ⇒ `ℕ , `ℕ ⊢ `ℕ
_ = ` S Z · ` Z

-- Previously: ∅ , "s" ⦂ `ℕ ⇒ `ℕ , "z" ⦂ `ℕ ⊢ ` "s" · (` "s" · ` "z") ⦂  `ℕ
_ : ∅ , `ℕ ⇒ `ℕ , `ℕ ⊢ `ℕ
_ = ` S Z · (` S Z · ` Z)

-- Previously: ∅ , "s" ⦂ `ℕ ⇒ `ℕ ⊢ (ƛ "z" ⇒ ` "s" · (` "s" · ` "z")) ⦂  `ℕ ⇒ `ℕ
_ : ∅ , `ℕ ⇒ `ℕ ⊢ `ℕ ⇒ `ℕ
_ = ƛ (` S Z · (` S Z · ` Z ))

-- Previously: ∅ ⊢ ƛ "s" ⇒ ƛ "z" ⇒ ` "s" · (` "s" · ` "z")) ⦂  (`ℕ ⇒ `ℕ) ⇒ `ℕ ⇒ `ℕ
_ : ∅ ⊢ (`ℕ ⇒ `ℕ) ⇒ `ℕ ⇒ `ℕ
_ = ƛ (ƛ ` S Z · (` S Z · ` Z))

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

-- Can rewrite above examples more compactly, e.g.:
_ : ∅ ⊢ (`ℕ ⇒ `ℕ) ⇒ `ℕ ⇒ `ℕ
_ = ƛ ƛ (# 1 · (# 1 · # 0))

-- Test examples

-- Two plus two on naturals
two : ∀ {Γ} → Γ ⊢ `ℕ
two = `suc `suc `zero

plus : ∀ {Γ} → Γ ⊢ `ℕ ⇒ `ℕ ⇒ `ℕ
plus = μ ƛ ƛ (case (# 1) (# 0) (`suc (# 3 · # 0 · # 1)))

2+2 : ∀ {Γ} → Γ ⊢ `ℕ
2+2 = plus · two · two

-- Two plus two on church numerals
Ch : Type → Type
Ch A = (A ⇒ A) ⇒ A ⇒ A

twoᶜ : ∀ {Γ A} → Γ ⊢ Ch A
twoᶜ = ƛ ƛ (# 1 · (# 1 · # 0))

plusᶜ : ∀ {Γ A} → Γ ⊢ Ch A ⇒ Ch A ⇒ Ch A
plusᶜ = ƛ ƛ ƛ ƛ (# 3 · # 1 · (# 2 · # 1 · # 0))

sucᶜ : ∀ {Γ} → Γ ⊢ `ℕ ⇒ `ℕ
sucᶜ = ƛ `suc (# 0)

2+2ᶜ : ∀ {Γ} → Γ ⊢ `ℕ
2+2ᶜ = plusᶜ · twoᶜ · twoᶜ · sucᶜ · `zero


-- Exercise: mul
-- mul : Term
-- mul = μ "×" ⇒ ƛ "m" ⇒ ƛ "n" ⇒
--         case ` "m"
--           [zero⇒ `zero
--           |suc "m" ⇒ plus · ` "n" · (` "×" · ` "m" · ` "n") ]

mul : ∀ {Γ} → Γ ⊢ `ℕ ⇒ `ℕ ⇒ `ℕ
mul = μ ƛ ƛ (case (# 1) `zero (plus · # 1 · (# 3 · # 0 · # 1)))
