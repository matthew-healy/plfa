module plfa.part1.Induction where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_)

-- Exercise: operators
-- Set union and intersection on P = Powerset({0, 1, 2})
-- Identity: n ∪ ∅ ≡ n and ∅ ∪ n ≡ n, n ∩ {0, 1, 2} ≡ n and {0, 1, 2} ∩ n ≡ n
-- Associativity: (m ∪ n) ∪ p ≡ m ∪ (n ∪ p) and (m ∩ n) ∩ p ≡ m ∩ (n ∩ p)
-- Commutativity: (m ∪ n) ∩ p ≡ (m ∩ p) ∪ (n ∩ p) and m ∩ (n ∪ p) ≡ (m ∩ n) ∪ (m ∩ p)

-- Function composition is associative but not commutative.
-- (f ∘ g) ∘ h = f ∘ (g ∘ h)
-- id is identity function
-- f ∘ g ≠ g ∘ f (it might not even be a valid composition)

_ : (3 + 4) + 5 ≡ 3 + (4 + 5)
_ =
  begin (3 + 4) + 5
    ≡⟨⟩ 7 + 5
    ≡⟨⟩ 12
    ≡⟨⟩ 3 + 9
    ≡⟨⟩ 3 + (4 + 5) ∎

+-assoc : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
+-assoc zero n p =
  begin (zero + n) + p
    ≡⟨⟩ n + p
    ≡⟨⟩ zero + (n + p) ∎
+-assoc (suc m) n p =
  begin ((suc m) + n) + p
    ≡⟨⟩ suc (m + n) + p
    ≡⟨⟩ suc ((m + n) + p)
    ≡⟨ cong suc (+-assoc m n p) ⟩ -- applying inductive case
        suc (m + (n + p))
    ≡⟨⟩ (suc m) + (n + p) ∎

-- a lemma used to prove commutativity of +
+-identityʳ : ∀ (m : ℕ) → m + zero ≡ m
+-identityʳ zero =
  begin zero + zero
    ≡⟨⟩ zero ∎
+-identityʳ (suc m) =
  begin suc m + zero
    ≡⟨⟩ suc (m + zero)
    ≡⟨ cong suc (+-identityʳ m) ⟩ -- applying inductive case
        suc m ∎

-- a lemma used to prove commutativity of +
+-suc : ∀ (m n : ℕ) → m + suc n ≡ suc (m + n)
+-suc zero n =
  begin zero + suc n
    ≡⟨⟩ suc n
    ≡⟨⟩ suc (zero + n) ∎
+-suc (suc m) n =
  begin suc m + suc n
    ≡⟨⟩ suc (m + suc n)
    ≡⟨ cong suc (+-suc m n) ⟩
        suc (suc (m + n))
    ≡⟨⟩ suc (suc m + n) ∎

-- proof that + is commutative on ℕ
+-comm : ∀ (m n : ℕ) → m + n ≡ n + m
+-comm m zero =
  begin m + zero
    ≡⟨ +-identityʳ m ⟩
        m
    ≡⟨⟩ zero + m ∎
+-comm m (suc n) =
  begin m + (suc n)
    ≡⟨ +-suc m n ⟩
        suc (m + n)
    ≡⟨ cong suc (+-comm m n) ⟩
        suc (n + m)
    ≡⟨⟩ suc n + m ∎

+-rearrange : ∀ (m n p q : ℕ) → (m + n) + (p + q) ≡ m + (n + p) + q
+-rearrange m n p q =
  begin
    (m + n) + (p + q)
  ≡⟨ +-assoc m n (p + q) ⟩
    m + (n + (p + q))
  ≡⟨ cong (m +_) (sym (+-assoc n p q)) ⟩
    m + ((n + p) + q)
  ≡⟨ sym (+-assoc m (n + p) q) ⟩
    (m + (n + p)) + q
  ∎

-- Exercise: finite-+-assoc (stretch)
-- In the beginning we know nothing about associativity.
-- On the first day, we know 0.
-- 0 : ℕ
-- On the second day, we know 1 and associativity of sums yielding 0.
-- 1 : ℕ
-- (0 + 0) + 0 = 0 + (0 + 0)
-- On the third day, we know 2 and associativity of sums yielding 1.
-- 2 : ℕ
-- (1 + 0) + 0 = 1 + (0 + 0), (0 + 1) + 0 = 0 + (1 + 0), (0 + 0) + 1 = 0 + (0 + 1)
-- On the fourth day, we know 3 and associativity of sums yielding 2.
-- 3 : ℕ
-- (2 + 0) + 0 = 2 + (0 + 0), (0 + 2) + 0 = 0 + (2 + 0), (0 + 0) + 2 = 0 + (0 + 2),
-- (1 + 1) + 0 = 1 + (1 + 0), (1 + 0) + 1 = 1 + (0 + 1), (0 + 1) + 1 =  0 + (1 + 1)

+-assoc' : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
+-assoc' zero n p = refl
+-assoc' (suc m) n p rewrite +-assoc' m n p = {!   !}

+-identity' : ∀ (n : ℕ) → n + zero ≡ n
+-identity' zero = refl
+-identity' (suc n) rewrite +-identity' n = refl

+-suc' : ∀ (m n : ℕ) → m + suc n ≡ suc (m + n)
+-suc' zero n = refl
+-suc' (suc m) n rewrite +-suc' m n = refl

+-comm' : ∀ (m n : ℕ) → m + n ≡ n + m
+-comm' m zero rewrite +-identity' m = refl
+-comm' m (suc n) rewrite +-suc' m n | +-comm' m n = refl
