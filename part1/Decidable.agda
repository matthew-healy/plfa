module plfa.part1.Decidable where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Negation using () renaming (contradiction to ¬¬-intro)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import plfa.part1.Relations using (_<_; z<s; s<s)
open import plfa.part1.Isomorphism using (_⇔_)

-- Evidence vs computation

infix 4 _≤_

data _≤_ : ℕ → ℕ → Set where
  z≤n : ∀ {n : ℕ} → zero ≤ n
  s≤s : ∀ {m n : ℕ} → m ≤ n → suc m ≤ suc n

_ : 2 ≤ 4
_ = s≤s (s≤s z≤n)

¬4≤2 : ¬ (4 ≤ 2)
¬4≤2 (s≤s (s≤s ()))

data Bool : Set where
  true  : Bool
  false : Bool

infix 4 _≤ᵇ_

_≤ᵇ_ : ℕ → ℕ → Bool
zero ≤ᵇ n = true
suc m ≤ᵇ zero = false
suc m ≤ᵇ suc n = m ≤ᵇ n

_ : (2 ≤ᵇ 4) ≡ true
_ = begin
  2 ≤ᵇ 4 ≡⟨⟩
  1 ≤ᵇ 3 ≡⟨⟩
  0 ≤ᵇ 2 ≡⟨⟩
  true   ∎

_ : (4 ≤ᵇ 2) ≡ false
_ = begin
  4 ≤ᵇ 2 ≡⟨⟩
  3 ≤ᵇ 1 ≡⟨⟩
  2 ≤ᵇ 0 ≡⟨⟩
  false  ∎

-- Relating evidence and computation

T : Bool → Set
T true  = ⊤
T false = ⊥

T→≡ : ∀ (b : Bool) → T b → b ≡ true
T→≡ true  tt = refl
T→≡ false ()

≡→T : ∀ {b : Bool} → b ≡ true → T b
≡→T refl = tt

≤ᵇ→≤ : ∀ (m n : ℕ) → T (m ≤ᵇ n) → m ≤ n
≤ᵇ→≤ zero n tt = z≤n
≤ᵇ→≤ (suc m) (suc n) t = s≤s (≤ᵇ→≤ m n t)

≤→≤ᵇ : ∀ {m n : ℕ} → m ≤ n → T (m ≤ᵇ n)
≤→≤ᵇ z≤n       = tt
≤→≤ᵇ (s≤s m≤n) = ≤→≤ᵇ m≤n

-- The best of both worlds

data Dec (A : Set): Set where
  yes :   A → Dec A
  no  : ¬ A → Dec A

¬s≤z : ∀ {m : ℕ} → ¬ (suc m ≤ zero)
¬s≤z ()

¬s≤s : ∀ {m n : ℕ} → ¬ (m ≤ n) → ¬ (suc m ≤ suc n)
¬s≤s ¬m≤n (s≤s m≤n) = ¬m≤n m≤n

_≤?_ : ∀ (m n : ℕ) → Dec (m ≤ n)
zero ≤? n = yes z≤n
suc m ≤? zero = no ¬s≤z
suc m ≤? suc n with m ≤? n
...               | yes m≤n = yes (s≤s m≤n)
...               | no ¬m≤n = no (¬s≤s ¬m≤n)

-- Exercise: _<?_

¬z<z : ¬ (zero < zero)
¬z<z ()

¬s<z : ∀ {n : ℕ} → ¬ (suc n < zero)
¬s<z ()

¬s<s : ∀ {m n : ℕ} → ¬ (m < n) → ¬ (suc m < suc n)
¬s<s ¬m<n (s<s m<n) = ¬m<n m<n

_<?_ : ∀ (m n : ℕ) → Dec (m < n)
zero <? zero = no ¬z<z
zero <? suc n = yes z<s
suc m <? zero = no ¬s<z
suc m <? suc n with m <? n
...               | yes m<n = yes (s<s m<n)
...               | no ¬m<n = no (¬s<s ¬m<n)

-- Exercise: _≡ℕ?_

¬s≡z : ∀ {m : ℕ} → ¬ (zero ≡ suc m)
¬s≡z ()

¬z≡s : ∀ {m : ℕ} → ¬ (suc m ≡ zero)
¬z≡s ()

¬s≡s : ∀ {m n : ℕ} → ¬ (m ≡ n) → ¬ (suc m ≡ suc n)
¬s≡s ¬m≡n refl = ¬m≡n refl

_≡ℕ?_ : ∀ (m n : ℕ) → Dec (m ≡ n)
zero ≡ℕ? zero = yes refl
zero ≡ℕ? suc n = no ¬s≡z
suc m ≡ℕ? zero = no ¬z≡s
suc m ≡ℕ? suc n with m ≡ℕ? n
...                | yes m≡n = yes (Eq.cong suc m≡n)
...                | no ¬m≡n = no (¬s≡s ¬m≡n)

-- Decidables from booleans, and booleans from decidables

_≤?′_ : ∀ (m n : ℕ) → Dec (m ≤ n)
m ≤?′ n with m ≤ᵇ n | ≤ᵇ→≤ m n | ≤→≤ᵇ {m} {n}
...        | true   | p        | _            = yes (p tt)
...        | false  | _        | ¬p           = no ¬p


⌊_⌋ : ∀ {A : Set} → Dec A → Bool
⌊ yes x ⌋ = true
⌊ no ¬x ⌋ = false

_≤ᵇ′_  : ℕ → ℕ → Bool
m ≤ᵇ′ n = ⌊ m ≤? n ⌋

toWitness : ∀ {A : Set} {D : Dec A} → T ⌊ D ⌋ → A
toWitness {A} {yes x} tt = x
toWitness {A} {no ¬x} ()

fromWitness : ∀ {A : Set} {D : Dec A} → A → T ⌊ D ⌋
fromWitness {A} {yes x} _ = tt
fromWitness {A} {no ¬x} x = ¬x x

≤ᵇ′→≤ : ∀ {m n : ℕ} → T (m ≤ᵇ′ n) → m ≤ n
≤ᵇ′→≤ = toWitness

≤→≤ᵇ′ : ∀ {m n : ℕ} → m ≤ n → T (m ≤ᵇ′ n)
≤→≤ᵇ′ = fromWitness

-- Logical connectives

-- And
infixr 6 _∧_

_∧_ : Bool → Bool → Bool
true ∧ true = true
_ ∧ false = false
false ∧ _ = false

infixr 6 _×-dec_

_×-dec_ : ∀ {A B : Set} → Dec A → Dec B → Dec (A × B)
yes x ×-dec yes y = yes ⟨ x , y ⟩
_     ×-dec no ¬y = no λ{ ⟨ x , y ⟩ → ¬y y }
no ¬x ×-dec _     = no λ{ ⟨ x , y ⟩ → ¬x x }

-- Or
infixr 5 _∨_

_∨_ : Bool → Bool → Bool
true  ∨ _     = true
_     ∨ true  = true
false ∨ false = false

infixr 5 _⊎-dec_

_⊎-dec_ : ∀ {A B : Set} → Dec A → Dec B → Dec (A ⊎ B)
yes x ⊎-dec _     = yes (inj₁ x)
_     ⊎-dec yes y = yes (inj₂ y)
no ¬x ⊎-dec no ¬y = no λ{ (inj₁ x) → ¬x x
                        ; (inj₂ y) → ¬y y
                        }

-- Not
not : Bool → Bool
not true  = false
not false = true

¬? : ∀ {A : Set} → Dec A → Dec (¬ A)
¬? (yes x) = no (¬¬-intro x)
¬? (no ¬x) = yes ¬x

-- Implies
_⊃_ : Bool → Bool → Bool
_     ⊃ true  = true
false ⊃ _     = true
true  ⊃ false = false

_→-dec_ : ∀ {A B : Set} → Dec A → Dec B → Dec (A → B)
_     →-dec yes y = yes (λ _ → y)
no ¬x →-dec _     = yes (λ x → ⊥-elim (¬x x))
yes x →-dec no ¬y = no  (λ f → ¬y (f x))

-- Exercise: erasure

∧-× : ∀ {A B : Set} (x : Dec A) (y : Dec B) → ⌊ x ⌋ ∧ ⌊ y ⌋ ≡ ⌊ x ×-dec y ⌋
∧-× (yes x) (yes y) = refl
∧-× (yes x) (no ¬y) = refl
∧-× (no ¬x) (yes y) = refl
∧-× (no ¬x) (no ¬y) = refl

∨-⊎ : ∀ {A B : Set} (x : Dec A) (y : Dec B) → ⌊ x ⌋ ∨ ⌊ y ⌋ ≡ ⌊ x ⊎-dec y ⌋
∨-⊎ (yes x) (yes y) = refl
∨-⊎ (yes x) (no ¬y) = refl
∨-⊎ (no ¬x) (yes x) = refl
∨-⊎ (no ¬x) (no x)  = refl

not-¬ : ∀ {A : Set} (x : Dec A) → not ⌊ x ⌋ ≡ ⌊ ¬? x ⌋
not-¬ (yes x) = refl
not-¬ (no ¬x) = refl

-- Exercise: iff-erasure

_iff_ : Bool → Bool → Bool
true  iff true  = true
false iff false = true
true  iff false = false
false iff true  = false

_⇔-dec_ : ∀ {A B : Set} → Dec A → Dec B → Dec (A ⇔ B)
yes x ⇔-dec yes y = yes record { to = λ{ _ → y } ; from = λ{ _ → x } }
no ¬x ⇔-dec no ¬y = yes record { to = λ{ x → ⊥-elim (¬x x) } ; from = λ{ y → ⊥-elim (¬y y) }}
yes x ⇔-dec no ¬y = no λ{ record { to = to ; from = from } → ¬y (to x) }
no ¬x ⇔-dec yes y = no λ{ record { to = to ; from = from } → ¬x (from y) }

iff-⇔ : ∀ {A B : Set} (x : Dec A) (y : Dec B) → ⌊ x ⌋ iff ⌊ y ⌋ ≡ ⌊ x ⇔-dec y ⌋
iff-⇔ (yes x) (yes y) = refl
iff-⇔ (no ¬x) (no ¬y) = refl
iff-⇔ (yes x) (no ¬y) = refl
iff-⇔ (no ¬x) (yes y) = refl


-- Proof by Reflection

minus : (m n : ℕ) (n≤m : n ≤ m) → ℕ
minus m       zero    _         = m
minus (suc m) (suc n) (s≤s n≤m) = minus m n n≤m

_ : minus 5 3 (s≤s (s≤s (s≤s z≤n))) ≡ 2
_ = refl

_-_ : (m n : ℕ) {n≤m : T ⌊ n ≤? m ⌋} → ℕ
_-_ m n {n≤m} = minus m n (toWitness n≤m)

_ : 5 - 3 ≡ 2
_ = refl

-- Stdlib has the following synonym for T ⌊ ? ⌋
True : ∀ {Q} → Dec Q → Set
True Q = T ⌊ Q ⌋

-- Exercise: False

False : ∀ {Q} → Dec Q → Set
False Q = T (not ⌊ Q ⌋)

toWitnessFalse : ∀ {A : Set} {D : Dec A} → False D → ¬ A
toWitnessFalse {A} {no ¬x} tt = ¬x

fromWitnessFalse : ∀ {A : Set} {D : Dec A} → ¬ A → False D
fromWitnessFalse {A} {yes x} ¬x = ⊥-elim (¬x x)
fromWitnessFalse {A} {no ¬x} ¬x′ = tt
