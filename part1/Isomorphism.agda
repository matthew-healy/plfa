module plfa.part1.Isomorphism where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; cong-app)
open Eq.≡-Reasoning
open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Data.Nat.Properties using (+-comm; +-identityʳ)

-- Function composition
_∘_ : ∀ {A B C : Set} → (B → C) → (A → B) → (A → C)
(g ∘ f) x = g (f x)

-- Function composition via lambda expressions
_∘′_ : ∀ {A B C : Set} → (B → C) → (A → B) → (A → C)
g ∘′ f = λ x → g (f x)

-- Extensionality
-- Means: the only way to distinguish functions is by applying them.

postulate
  extensionality : ∀ {A B : Set} {f g : A → B}
    → (∀ (x : A) → f x ≡ g x)
      -----------------------
    → f ≡ g

-- Let's say we had two definitions of addition, _+_ from Data.Nat and..
_+′_ : ℕ → ℕ → ℕ
m +′ zero  = m
m +′ suc n = suc (m +′ n)

-- Easy to show both operators return the same result given the same arguments:

same-app : ∀ (m n : ℕ) → m +′ n ≡ m + n
same-app m n rewrite +-comm m n = helper m n
  where
  helper : ∀ (m n : ℕ) → m +′ n ≡ n + m
  helper m zero    = refl
  helper m (suc n) = cong suc (helper m n)

same : _+′_ ≡ _+_
same = extensionality (λ m → extensionality (λ n → same-app m n))

-- Extensionality for dependent functions
postulate
  ∀-extensionality : ∀ {A : Set} {B : A → Set} {f g : ∀ (x : A) → B x}
    → (∀ (x : A) → f x ≡ g x)
      -----------------------
    → f ≡ g

-- Isomorphism

infix 0 _≃_
record _≃_ (A B : Set) : Set where
  field
    to      : A → B
    from    : B → A
    from∘to : ∀ (x : A) → from (to x) ≡ x
    to∘from : ∀ (y : B) → to (from y) ≡ y
open _≃_ -- makes to, from etc. available without namespacing.

-- The above record is similar to the following single-constructor data declaration
data _≃′_ (A B : Set) : Set where
  mk-≃′ : ∀ (to : A → B) →
          ∀ (from : B → A) →
          ∀ (from∘to : (∀ (x : A) → from (to x) ≡ x)) →
          ∀ (to∘from : (∀ (y : B) → to (from y) ≡ y)) →
          A ≃′ B

to′ : ∀ {A B : Set} → (A ≃′ B) → (A → B)
to′ (mk-≃′ f g g∘f f∘g) = f

from′ : ∀ {A B : Set} → (A ≃′ B) → (B → A)
from′ (mk-≃′ f g g∘f f∘g) = g

from∘to′ : ∀ {A B : Set} → (A≃B : A ≃′ B) → (∀ (x : A) → from′ A≃B (to′ A≃B x) ≡ x)
from∘to′ (mk-≃′ f g g∘f f∘g) = g∘f

to∘from′ : ∀ {A B : Set} → (A≃B : A ≃′ B) → (∀ (y : B) → to′ A≃B (from′ A≃B y) ≡ y)
to∘from′ (mk-≃′ f g g∘f f∘g) = f∘g

-- Isomorphism is an equivalence

≃-refl : ∀ {A : Set}
    -----
  → A ≃ A
≃-refl = record
  { to      = λ{x → x}
  ; from    = λ{y → y}
  ; from∘to = λ{x → refl}
  ; to∘from = λ{y → refl}
  }

≃-sym : ∀ {A B : Set}
  → A ≃ B
    -----
  → B ≃ A
≃-sym A≃B = record
  { to      = from A≃B
  ; from    = to A≃B
  ; from∘to = to∘from A≃B
  ; to∘from = from∘to A≃B
  }

≃-trans : ∀ {A B C : Set}
  → A ≃ B
  → B ≃ C
    -----
  → A ≃ C
≃-trans A≃B B≃C = record
  { to = (to B≃C) ∘ (to A≃B)
  ; from = (from A≃B) ∘ (from B≃C)
  ; from∘to = λ{x → begin
    from A≃B (from B≃C (to B≃C (to A≃B x))) ≡⟨ cong (from A≃B) (from∘to B≃C (to A≃B x)) ⟩
    from A≃B (to A≃B x) ≡⟨ from∘to A≃B x ⟩
    x ∎}
  ; to∘from = λ{y → begin
    to B≃C (to A≃B (from A≃B (from B≃C y))) ≡⟨ cong (to B≃C) (to∘from A≃B (from B≃C y)) ⟩
    to B≃C (from B≃C y) ≡⟨ to∘from B≃C y ⟩
    y ∎}
  }

-- Equational reasoning for isomorphism

module ≃-Reasoning where

  infix  1 ≃-begin_
  infixr 2 _≃⟨_⟩_
  infix  3 _≃-∎

  ≃-begin_ : ∀ {A B : Set}
   → A ≃ B
    ------
   → A ≃ B
  ≃-begin A≃B = A≃B

  _≃⟨_⟩_ : ∀ (A : Set) {B C : Set}
    → A ≃ B
    → B ≃ C
      -----
    → A ≃ C
  A ≃⟨ A≃B ⟩ B≃C = ≃-trans A≃B B≃C

  _≃-∎ : ∀ (A : Set)
      -----
    → A ≃ A
  A ≃-∎ = ≃-refl

open ≃-Reasoning

-- Embedding

infix 0 _≲_
record _≲_ (A B : Set) : Set where
  field
    to      : A → B
    from    : B → A
    from∘to : ∀ (x : A) → from (to x) ≡ x
open _≲_

≲-refl : ∀ {A : Set} → A ≲ A
≲-refl = record
  { to      = λ{x → x}
  ; from    = λ{y → y}
  ; from∘to = λ{x → refl}
  }

≲-trans : ∀ {A B C : Set} → A ≲ B → B ≲ C → A ≲ C
≲-trans A≲B B≲C = record
  { to = λ{x → to B≲C (to A≲B x)}
  ; from = λ{y → from A≲B (from B≲C y)}
  ; from∘to = λ{x → begin
    from A≲B (from B≲C (to B≲C (to A≲B x))) ≡⟨ cong (from A≲B) (from∘to B≲C (to A≲B x)) ⟩
    from A≲B (to A≲B x) ≡⟨ from∘to A≲B x ⟩
    x ∎}
  }

≲-antisym : ∀ {A B : Set}
  → (A≲B : A ≲ B)
  → (B≲A : B ≲ A)
  → (to A≲B ≡ from B≲A)
  → (from A≲B ≡ to B≲A)
    -------------------
  → A ≃ B
≲-antisym A≲B B≲A to≡from from≡to = record
  { to = to A≲B
  ; from = from A≲B
  ; from∘to = from∘to A≲B
  ; to∘from = λ{y → begin
    to A≲B (from A≲B y) ≡⟨ cong (to A≲B) (cong-app from≡to y) ⟩
    to A≲B (to B≲A y) ≡⟨ (cong-app to≡from (to B≲A y)) ⟩
    from B≲A (to B≲A y) ≡⟨ from∘to B≲A y ⟩
    y ∎}
  }

-- Equational reasoning for embedding

module ≲-Reasoning where

  infix  1 ≲-begin_
  infixr 2 _≲⟨_⟩_
  infix  3 _≲-∎

  ≲-begin_ : ∀ {A B : Set}
    → A ≲ B
      -----
    → A ≲ B
  ≲-begin A≲B = A≲B

  _≲⟨_⟩_ : ∀ (A : Set) {B C : Set}
    → A ≲ B
    → B ≲ C
      -----
    → A ≲ C
  A ≲⟨ A≲B ⟩ B≲C = ≲-trans A≲B B≲C

  _≲-∎ : ∀ (A : Set)
      -----
    → A ≲ A
  A ≲-∎ = ≲-refl

open ≲-Reasoning

-- Exercise: ≃-implies-≲
≃-implies-≲ : ∀ {A B : Set}
  → A ≃ B
    -----
  → A ≲ B
≃-implies-≲ A≃B = record
  { to = to A≃B
  ; from = from A≃B
  ; from∘to = from∘to A≃B
  }

-- Exercise: _⇔_

record _⇔_ (A B : Set) : Set where
  field
    to   : A → B
    from : B → A

⇔-refl : ∀ {A : Set} → A ⇔ A
⇔-refl = record
  { to   = λ x → x
  ; from = λ x → x
  }

⇔-sym : ∀ {A B : Set}
  → A ⇔ B
    -----
  → B ⇔ A
⇔-sym A⇔B = record
  { to   = _⇔_.from A⇔B
  ; from = _⇔_.to A⇔B
  }

⇔-trans : ∀ {A B C : Set}
  → A ⇔ B
  → B ⇔ C
    -----
  → A ⇔ C
⇔-trans A⇔B B⇔C = record
  { to = λ x → _⇔_.to B⇔C (_⇔_.to A⇔B x)
  ; from = λ x → _⇔_.from A⇔B (_⇔_.from B⇔C x)
  }

-- Exercise Bin-embedding
data Bin : Set where
  ⟨⟩ : Bin
  _O : Bin → Bin
  _I : Bin → Bin

inc : Bin → Bin
inc ⟨⟩ = ⟨⟩ I
inc (b O) = (b I)
inc (b I) = (inc b) O

ℕ-to-Bin : ℕ → Bin
ℕ-to-Bin zero = ⟨⟩ O
ℕ-to-Bin (suc n) = inc (ℕ-to-Bin n)

ℕ-from-Bin : Bin → ℕ
ℕ-from-Bin ⟨⟩    = zero
ℕ-from-Bin (n O) = 2 * (ℕ-from-Bin n)
ℕ-from-Bin (n I) = 1 + 2 * (ℕ-from-Bin n)

inc-suc-equiv : ∀ (b : Bin) → ℕ-from-Bin (inc b) ≡ suc (ℕ-from-Bin b)
inc-suc-equiv ⟨⟩ = refl
inc-suc-equiv (b O) = refl
inc-suc-equiv (b I)
  rewrite inc-suc-equiv b
  | +-identityʳ (ℕ-from-Bin b)
  | +-comm (ℕ-from-Bin b) (suc (ℕ-from-Bin b)) = refl

from-to-inverse : ∀ (n : ℕ) → ℕ-from-Bin (ℕ-to-Bin n) ≡ n
from-to-inverse zero = refl
from-to-inverse (suc n) rewrite inc-suc-equiv (ℕ-to-Bin n) | from-to-inverse n = refl

ℕ-embeds-in-Bin : ℕ ≲ Bin
ℕ-embeds-in-Bin = record
  { to = ℕ-to-Bin
  ; from = ℕ-from-Bin
  ; from∘to = from-to-inverse
  }

-- ℕ-to-Bin and ℕ-from-Bin do not form an isomorpism because there are
-- countably-infinitely many members of Bin which represent each ℕ.
-- e.g. ⟨⟩ I, ⟨⟩ O I, ⟨⟩ O O I, ... all represent 1, which means:
-- ℕ-to-Bin (ℕ-from-Bin ⟨⟩ O I) ≢ ⟨⟩ O I

-- However the canonical representations of binary numbers are isomorphic to ℕ.
