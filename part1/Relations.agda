module plfa.part1.Relations where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-comm)

data _≤_ : ℕ → ℕ → Set where
  z≤n : ∀ { n : ℕ }
      --------
    → zero ≤ n

  s≤s : ∀ { m n : ℕ }
    → m ≤ n
      -------------
    → suc m ≤ suc n

_ : 2 ≤ 4
_ = s≤s (s≤s z≤n)

_ : 2 ≤ 4
_ = s≤s {1} {3} (s≤s {0} {2} (z≤n {2}))

infix 4 _≤_

inv-s≤s : ∀ { m n : ℕ }
  → suc m ≤ suc n
    -------------
  → m ≤ n
inv-s≤s (s≤s m≤n) = m≤n

inv-z≤n : ∀ { m : ℕ }
  → m ≤ zero
    --------
  → m ≡ zero
inv-z≤n z≤n = refl

-- Properties of orderings

-- Reflexive: ∀ (n : ℕ) → n ≤ n
-- Transitive: ∀ (m n p : ℕ) → (m ≤ n) ∧ (n ≤ p) → m ≤ p
-- Antisymmetric: ∀ (m n : ℕ) → (m ≤ n) ∧ (n ≤ m) → m ≡ n
-- Total: ∀ (m n : ℕ) → (m ≤ n) ∨ (n ≤ m)

-- Combinations of properties

-- Preorder: reflexive & transitive
-- Partial order: preorder & antisymmetric
-- Total order: partial order & total

-- Exercise: orderings
-- A preorder that is not a partial order:
-- let μ: ℤ → ℤ, μ(x) = x² and consider the relationship defined by:
-- m ≤′ n ⇔ μ(m) ≤ μ(n)
-- Reflexive: m ≤′ m since m² ≤ m²
-- Transitive: m ≤′ n ∧ n ≤′ p ⇔ m² ≤ n² ∧ n² ≤ p² ⇒ m² ≤ p²
-- Not antisymmetric: 4 ≤′ -4 and -4 ≤′ 4 but 4 ≢ -4.

-- A partial order that is not a total order: ≡
-- i.e. n ≡ n for any n
-- if n ≡ m and m ≡ p then n ≡ p
-- also if n ≡ m and m ≡ n then m ≡ n
-- however it's not true that either m ≡ n or n ≡ m for any m, n

-- Reflexivity of ≤
≤-refl : ∀ { n : ℕ }
    -----
  → n ≤ n
≤-refl {zero} = z≤n
≤-refl {suc n} = s≤s ≤-refl

-- Transitivity of ≤
≤-trans : ∀ { m n p : ℕ }
  → m ≤ n
  → n ≤ p
    -----
  → m ≤ p
-- Proof by induction on evidence that m ≤ n
-- i.e. either m ≤ n because m is zero (and so z≤n applies)
≤-trans z≤n       _         = z≤n
-- or m ≠ 0 in which case m = suc m' so s≤s applies.
-- (s≤s m≤n) (z≤n) doesn't make sense since we know n > 0
-- Now we can prove m ≤ p  by applying the inductive hypothesis
-- and then applying s≤s proves that suc m ≤ suc p.
≤-trans (s≤s m≤n) (s≤s n≤p) = s≤s (≤-trans m≤n n≤p)

-- Same example but with explicit parameters.
≤-trans′ : ∀ ( m n p : ℕ )
  → m ≤ n
  → n ≤ p
    -----
  → m ≤ p
≤-trans′ zero    _       _       z≤n       _         = z≤n
≤-trans′ (suc m) (suc n) (suc p) (s≤s m≤n) (s≤s n≤p) = s≤s (≤-trans′ m n p m≤n n≤p)

-- How can C-c C-l, C-c C-, and C-c C-r be leveraged to solve this?
-- You need to make sure you name the evidence before you add the type hole.
-- E.g. ≤-trans = ? won't work, but ≤-trans m≤n n≤p will.

-- Antisymmetry of ≤
≤-antisym : ∀ { m n : ℕ }
  → m ≤ n
  → n ≤ m
    -----
  → m ≡ n
≤-antisym z≤n z≤n = refl
≤-antisym (s≤s m≤n) (s≤s n≤m) = cong suc (≤-antisym m≤n n≤m)

-- Exercise: ≤-antisym-cases
-- The above proof omits cases where one argument is z≤n and one argument is s≤s.
-- Why is it okay to omit them?
--
-- Let's assume m≤n is z≤n, and n≤m is s≤s. The first assumption suggests m is zero.
-- However the second assumption suggests m is suc m′ for some m′ : ℕ. This is
-- a contradiction, and thus we can discard this case.
