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
