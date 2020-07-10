module plfa.part1.Naturals where

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

-- zero -- 0
-- suc zero -- 1
-- suc (suz zero) -- 2
-- ...
-- suc (suc (suc (suc (suc (suc (suc zero)))))) -- 7

{-# BUILTIN NATURAL ℕ #-}

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _∎)

_+_ : ℕ → ℕ → ℕ
zero + n = n
suc m + n = suc (m + n)

_ : 2 + 3 ≡ 5
_ =
  begin
    2 + 3
  ≡⟨⟩
    (suc (suc zero)) + (suc (suc (suc (zero))))
  ≡⟨⟩
    suc ((suc zero) + (suc (suc (suc zero))))
  ≡⟨⟩
    suc (suc (zero + (suc (suc (suc zero)))))
  ≡⟨⟩
    suc (suc (suc (suc (suc zero))))
  ≡⟨⟩
    5
  ∎

_ : 2 + 5 ≡ 7
_ =
  begin
    2 + 5
  ≡⟨⟩
    suc (1 + 5)
  ≡⟨⟩
    suc (suc (0 + 5))
  ≡⟨⟩
    suc (suc 5)
  ≡⟨⟩
    7
  ∎

_ : 3 + 5 ≡ 8
_ = refl

-- Exercise: +-example
_ = 3 + 4 ≡ 7
_ =
  begin 3 + 4
    ≡⟨⟩ (suc (2 + 4))
    ≡⟨⟩ (suc (suc (1 + 4)))
    ≡⟨⟩ (suc (suc (suc (0 + 4))))
    ≡⟨⟩ 7 ∎

_*_ : ℕ → ℕ → ℕ
zero    * n = zero
(suc m) * n = n + (m * n)

_ =
  begin 2 * 3
    ≡⟨⟩ 3 + (1 * 3)
    ≡⟨⟩ 3 + (3 + (0 * 3))
    ≡⟨⟩ 3 + (3 + 0)
    ≡⟨⟩ 6 ∎

-- Exercise: *-example
_ =
  begin 3 * 4
    ≡⟨⟩ 4 + (2 * 4)
    ≡⟨⟩ 4 + (4 + (1 * 4))
    ≡⟨⟩ 4 + (4 + (4 + (0 * 4)))
    ≡⟨⟩ 4 + (4 + (4 + 0))
    ≡⟨⟩ 12 ∎

-- Exercise: _^_
_^_ : ℕ → ℕ → ℕ
n ^ zero    = suc zero
m ^ (suc n) = m * (m ^ n)

_ =
  begin 3 ^ 4
    ≡⟨⟩ 3 * (3 ^ 3)
    ≡⟨⟩ 3 * (3 * (3 ^ 2))
    ≡⟨⟩ 3 * (3 * (3 * (3 ^ 1)))
    ≡⟨⟩ 3 * (3 * (3 * (3 * (3 ^ 0))))
    ≡⟨⟩ 3 * (3 * (3 * (3 * 1)))
    ≡⟨⟩ 3 * (3 * (3 * 3))
    ≡⟨⟩ 3 * (3 * 9)
    ≡⟨⟩ 3 * 27
    ≡⟨⟩ 81 ∎

-- "Monus"
_∸_ : ℕ → ℕ → ℕ
m       ∸ zero    = m
zero    ∸ suc n = zero
suc m ∸ suc n = m ∸ n

_ =
  begin 3 ∸ 2
    -- ≡⟨⟩ (suc 2) ∸ (suc 1)
    ≡⟨⟩ 2 ∸ 1
    -- ≡⟨⟩ (suc 1) ∸ (suc zero)
    ≡⟨⟩ 1 ∸ 0
    ≡⟨⟩ 1 ∎

_ =
  begin 2 ∸ 3
    ≡⟨⟩ (suc 1) ∸ (suc 2)
    ≡⟨⟩ 1 ∸ 2
    ≡⟨⟩ (suc zero) ∸ (suc 1)
    ≡⟨⟩ zero ∸ 1
    ≡⟨⟩ 0 ∎

-- Exercise: ∸-example

_ =
  begin 5 ∸ 3
    ≡⟨⟩ (suc 4) ∸ (suc 2)
    ≡⟨⟩ 4 ∸ 2
    ≡⟨⟩ (suc 3) ∸ (suc 1)
    ≡⟨⟩ 3 ∸ 1
    ≡⟨⟩ (suc 2) ∸ (suc 0)
    ≡⟨⟩ 2 ∸ 0
    ≡⟨⟩ 2 ∎

_ =
  begin 3 ∸ 5
    ≡⟨⟩ 2 ∸ 4
    ≡⟨⟩ 1 ∸ 3
    ≡⟨⟩ 0 ∸ 2
    ≡⟨⟩ 0 ∎

infixl 6 _+_ _∸_
infixl 7 _*_

{-# BUILTIN NATPLUS _+_ #-}
{-# BUILTIN NATTIMES _*_ #-}
{-# BUILTIN NATMINUS _∸_ #-}

-- Exercise: Bin (stretch)
data Bin : Set where
  ⟨⟩ : Bin
  _O : Bin → Bin
  _I : Bin → Bin

inc : Bin → Bin
inc ⟨⟩ = ⟨⟩ I
inc (b O) = (b I)
inc (b I) = (inc b) O

_ : inc (⟨⟩ I O I I) ≡ ⟨⟩ I I O O
_ =
  begin inc (⟨⟩ I O I I)
    ≡⟨⟩ inc (⟨⟩ I O I) O
    ≡⟨⟩ inc (⟨⟩ I O) O O
    ≡⟨⟩ ⟨⟩ I I O O ∎

_ = begin inc (⟨⟩ O) ≡⟨⟩ (⟨⟩ I) ∎ -- inc 0 == 1
_ = begin inc (⟨⟩ I) ≡⟨⟩ (inc ⟨⟩) O ≡⟨⟩ ⟨⟩ I O ∎ -- inc 1 == 2
_ = begin inc (⟨⟩ I O) ≡⟨⟩ ⟨⟩ I I ∎ -- inc 2 == 3
_ =
  begin inc (⟨⟩ I I)
    ≡⟨⟩ inc ((⟨⟩ I) I)
    ≡⟨⟩ (inc (⟨⟩ I)) O
    ≡⟨⟩ (inc ⟨⟩) O O
    ≡⟨⟩ ⟨⟩ I O O ∎ -- inc 3 == 4

to : ℕ → Bin
to zero = ⟨⟩ O
to (suc n) = inc (to n)

_ = begin to 0 ≡⟨⟩ ⟨⟩ O ∎
_ =
  begin to 1
    ≡⟨⟩ to (suc 0)
    ≡⟨⟩ inc (to 0)
    ≡⟨⟩ inc (⟨⟩ O)
    ≡⟨⟩ ⟨⟩ I ∎
_ =
  begin to 2
    ≡⟨⟩ to (suc 1)
    ≡⟨⟩ inc (to 1)
    ≡⟨⟩ inc (⟨⟩ I)
    ≡⟨⟩ ⟨⟩ I O ∎
_ =
  begin to 3
    ≡⟨⟩ to (suc 2)
    ≡⟨⟩ inc (to 2)
    ≡⟨⟩ inc (⟨⟩ I O)
    ≡⟨⟩ ⟨⟩ I I ∎
_ =
  begin to 4
    ≡⟨⟩ to (suc 3)
    ≡⟨⟩ inc (to 3)
    ≡⟨⟩ inc (⟨⟩ I I)
    ≡⟨⟩ ⟨⟩ I O O ∎

from : Bin → ℕ
from ⟨⟩    = zero
from (n O) = 2 * (from n)
from (n I) = 1 + 2 * (from n)

_ = begin from (⟨⟩ O) ≡⟨⟩ from ⟨⟩ ≡⟨⟩ zero ∎

_ =
  begin from (⟨⟩ I)
    ≡⟨⟩ 1 + 2 * (from ⟨⟩)
    ≡⟨⟩ 1 + 2 * 0
    ≡⟨⟩ 1 ∎

_ =
  begin from (⟨⟩ I O)
    ≡⟨⟩ 2 * (from (⟨⟩ I))
    ≡⟨⟩ 2 * (1 + 2 * (from ⟨⟩))
    ≡⟨⟩ 2 * (1 + (2 * 0))
    ≡⟨⟩ 2 * 1
    ≡⟨⟩ 2 ∎

_ =
  begin from (⟨⟩ I I)
    ≡⟨⟩ 1 + 2 * (from (⟨⟩ I))
    ≡⟨⟩ 1 + 2 * (1 + 2 * (from ⟨⟩))
    ≡⟨⟩ 1 + 2 * (1 + 2 * 0)
    ≡⟨⟩ 3 ∎

_ =
  begin from (⟨⟩ I O O)
    ≡⟨⟩ 2 * (from (⟨⟩ I O))
    ≡⟨⟩ 2 * (2 * (from (⟨⟩ I)))
    ≡⟨⟩ 2 * (2 * (1 + 2 * (from ⟨⟩)))
    ≡⟨⟩ 2 * (2 * (1 + 2 * 0))
    ≡⟨⟩ 4 ∎

-- import Data.Nat using (ℕ, zero; suc; _+_; _*_; _^_; _∸_)
