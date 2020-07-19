module plfa.part1.EqualityExercise where

-- Exercise ≤-Reasoning

data _≡_ { A : Set } (x : A) : A → Set where
  refl : x ≡ x

infix 4 _≡_

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

_+_ : ℕ → ℕ → ℕ
zero + n = n
suc m + n = suc (m + n)

postulate
  +-identityˡ : ∀ (m : ℕ) → zero + m ≡ m
  +-comm : ∀ (m n : ℕ) → m + n ≡ n + m

data _≤_ : ℕ → ℕ → Set where
  z≤n : ∀ { n : ℕ }
      --------
    → zero ≤ n

  s≤s : ∀ { m n : ℕ }
    → m ≤ n
      -------------
    → suc m ≤ suc n

infix 4 _≤_

trans : ∀ {x y z : ℕ}
  → x ≤ y
  → y ≤ z
    -----
  → x ≤ z
trans z≤n y≤z = z≤n
trans (s≤s x≤y) (s≤s y≤z) = s≤s (trans x≤y y≤z)

module ≤-Reasoning where
  infix  1 begin_
  infixr 2 _≡⟨⟩_ _≤⟨_⟩_ _≡⟨_⟩_
  infix  3 _∎

  begin_ : ∀ {x y : ℕ}
    → x ≤ y
      -----
    → x ≤ y
  begin x≤y = x≤y

  _≡⟨⟩_ : ∀ (x : ℕ) {y : ℕ}
    → x ≤ y
      -----
    → x ≤ y
  x ≡⟨⟩ x≤y = x≤y

  _≤⟨_⟩_ : ∀ (x : ℕ) {y z : ℕ}
    → x ≤ y
    → y ≤ z
      -----
    → x ≤ z
  x ≤⟨ x≤y ⟩ y≤z = trans x≤y y≤z

  _≡⟨_⟩_ : ∀ (m : ℕ) {n p : ℕ}
    → m ≡ n
    → n ≤ p
      -----
    → m ≤ p
  zero ≡⟨ refl ⟩ n≤p = z≤n
  suc m ≡⟨ refl ⟩ s≤s m≤n = s≤s m≤n

  _∎ : ∀ (x : ℕ)
      ----
    → x ≤ x
  zero ∎ = z≤n
  suc x ∎ = s≤s (x ∎)

open ≤-Reasoning

+-monoʳ-≤ : ∀ (n p q : ℕ)
  → p ≤ q
    -------------
  → n + p ≤ n + q
+-monoʳ-≤ zero p q p≤q = begin
    zero + p ≡⟨ +-identityˡ p ⟩
    p        ≤⟨ p≤q ⟩
    q        ≡⟨ +-identityˡ q ⟩
    zero + q ∎
+-monoʳ-≤ (suc n) p q p≤q = begin
    (suc n) + p ≡⟨⟩
    suc (n + p) ≤⟨ s≤s (+-monoʳ-≤ n p q p≤q) ⟩
    suc (n + q) ≡⟨⟩
    (suc n) + q ∎

+-monoˡ-≤ : ∀ (m n p : ℕ)
  → m ≤ n
    -------------
  → m + p ≤ n + p
+-monoˡ-≤ m n p m≤n = begin
  m + p ≡⟨ +-comm m p ⟩
  p + m ≤⟨ +-monoʳ-≤ p m n m≤n ⟩
  p + n ≡⟨ +-comm p n ⟩
  n + p ∎

+-mono-≤ : ∀ (m n p q : ℕ)
  → m ≤ n
  → p ≤ q
    -------------
  → m + p ≤ n + q
+-mono-≤ m n p q m≤n p≤q = begin
    m + p ≤⟨ +-monoˡ-≤ m n p m≤n ⟩
    n + p ≤⟨ +-monoʳ-≤ n p q p≤q ⟩
    n + q ∎
