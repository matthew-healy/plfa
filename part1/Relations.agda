module plfa.part1.Relations where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Data.Nat.Properties using (+-comm; *-comm)

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

-- Totality of ≤

data Total (m n : ℕ) : Set where

  forward :
      m ≤ n
      ---------
    → Total m n

  flipped :
      n ≤ m
      -----
    → Total m n

-- The above definition is "with parameters" (i.e. m and n). It is equivalent to
-- the indexed datatype:

data Total′ : ℕ → ℕ → Set where

  forward′ : ∀ { m n : ℕ }
    → m ≤ n
      ----------
    → Total′ m n

  flipped′ : ∀ { m n : ℕ }
    → n ≤ m
      --------
    → Total′ m n

-- Unlike an indexed datatype where indices can vary (e.g. zero ≤ n and suc m ≤ suc n)
-- a parameterised datatype must always use the same parameters (e.g. Total m n)

≤-total : ∀ (m n : ℕ) → Total m n
≤-total zero n = forward z≤n
≤-total (suc m) zero = flipped z≤n
≤-total (suc m) (suc n) with ≤-total m n
...                        | forward m≤n = forward (s≤s m≤n)
...                        | flipped n≤m = flipped (s≤s n≤m)

-- The with clause is equivalent to defining a helper function. i.e. it's equivalent to:

≤-total′ : ∀ (m n : ℕ) → Total m n
≤-total′ zero n = forward z≤n
≤-total′ (suc m) zero = flipped z≤n
≤-total′ (suc m) (suc n) = helper (≤-total′ m n)
  where
  helper : Total m n → Total (suc m) (suc n)
  helper (forward m≤n) = forward (s≤s m≤n)
  helper (flipped n≤m) = flipped (s≤s n≤m)

-- Monotonicity
+-monoʳ-≤ : ∀ (n p q : ℕ)
  → p ≤ q
    -----
  → n + p ≤ n + q
+-monoʳ-≤ zero p q p≤q = p≤q
+-monoʳ-≤ (suc n) p q p≤q = s≤s (+-monoʳ-≤ n p q p≤q)

+-monoˡ-≤ : ∀ (m n p : ℕ)
  → m ≤ n
    -------------
  → m + p ≤ n + p
+-monoˡ-≤ m n p m≤n rewrite +-comm m p | +-comm n p = +-monoʳ-≤ p m n m≤n

+-mono-≤ : ∀ (m n p q : ℕ)
  → m ≤ n
  → p ≤ q
    -------------
  → m + p ≤ n + q
+-mono-≤ m n p q m≤n p≤q = ≤-trans (+-monoˡ-≤ m n p m≤n) (+-monoʳ-≤ n p q p≤q)

-- Exercise: *-mono-≤

*-monoʳ-≤ : ∀ (n p q : ℕ)
  → p ≤ q
    -------------
  → n * p ≤ n * q
*-monoʳ-≤ zero p q p≤q = z≤n
*-monoʳ-≤ (suc n) p q p≤q = +-mono-≤ p q (n * p) (n * q) p≤q (*-monoʳ-≤ n p q p≤q)

*-monoˡ-≤ : ∀ (m n p : ℕ)
  → m ≤ n
    -------------
  → m * p ≤ n * p
*-monoˡ-≤ m n p m≤n rewrite *-comm m p | *-comm n p = *-monoʳ-≤ p m n m≤n

*-mono-≤ : ∀ (m n p q : ℕ)
  → m ≤ n
  → p ≤ q
    -------------
  → m * p ≤ n * q
*-mono-≤ m n p q m≤n p≤q = ≤-trans (*-monoˡ-≤ m n p m≤n) (*-monoʳ-≤ n p q p≤q)
