module plfa.part1.Connectives where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning
open import Data.Nat using (ℕ)
open import Function using (_∘_)
open import plfa.part1.Isomorphism using (_≃_; _≲_; _⇔_; extensionality)
open plfa.part1.Isomorphism.≃-Reasoning

-- Conjunction is product

data _×_ (A B : Set) : Set where
  ⟨_,_⟩ : A → B → A × B

proj₁ : ∀ {A B : Set}
  → A × B
    -----
  → A
proj₁ ⟨ x , y ⟩ = x

proj₂ : ∀ {A B : Set}
  → A × B
    -----
  → B
proj₂ ⟨ x , y ⟩ = y

-- ⟨_,_⟩ is an introduction - it shows how to define the connective
-- proj₁ and proj₂ are eliminators - they tell us how to use the connective

-- Applying introduction to eliminations is identity
η-× : ∀ {A B : Set} (w : A × B) → ⟨ proj₁ w , proj₂ w ⟩ ≡ w
η-× ⟨ x , y ⟩ = refl

infixr 2 _×_

-- Can also declare conjunction as a record type:
record _×′_ (A B : Set) : Set where
  constructor ⟨_,_⟩′
  field
    proj₁′ : A
    proj₂′ : B
open _×′_

-- Don't need to pattern match with record definition
η-×′ : ∀ {A B : Set} (w : A ×′ B) → ⟨ proj₁′ w , proj₂′ w ⟩′ ≡ w
η-×′ x = refl

-- Product is commutative and associative up to isomorphism

×-comm : ∀ {A B : Set} → A × B ≃ B × A
×-comm = record
  { to = λ{ ⟨ x , y ⟩ → ⟨ y , x ⟩ }
  ; from = λ{ ⟨ y , x ⟩ → ⟨ x , y ⟩ }
  ; from∘to = λ{ ⟨ x , y ⟩ → refl }
  ; to∘from = λ{ ⟨ y , x ⟩ → refl }
  }

×-assoc : ∀ {A B C : Set} → (A × B) × C ≃ A × (B × C)
×-assoc = record
  { to      = λ{ ⟨ ⟨ x , y ⟩ , z ⟩ → ⟨ x , ⟨ y , z ⟩ ⟩ }
  ; from    = λ{ ⟨ x , ⟨ y , z ⟩ ⟩ → ⟨ ⟨ x , y ⟩ , z ⟩ }
  ; from∘to = λ{ ⟨ ⟨ x , y ⟩ , z ⟩ → refl }
  ; to∘from = λ{ ⟨ x , ⟨ y , z ⟩ ⟩ → refl }
  }

-- Exercise: ⇔≃×

⇔≃× : ∀ {A B : Set} → A ⇔ B ≃ (A → B) × (B → A)
⇔≃× = record
  { to      = λ{ record { to = to ; from = from } → ⟨ to , from ⟩ }
  ; from    = λ{ ⟨ to , from ⟩ → record { to = to ; from = from } }
  ; from∘to = λ{ record { to = to ; from = from } → refl }
  ; to∘from = λ{ ⟨ to , from ⟩ → refl }
  }

-- Truth is unit

data ⊤ : Set where
  tt : ⊤

η-⊤ : ∀ (w : ⊤) → tt ≡ w
η-⊤ tt = refl

-- Can also declare as empty record
record ⊤′ : Set where
  constructor tt′

η-⊤′ : ∀ (w : ⊤′) → tt′ ≡ w
η-⊤′ w = refl

-- Unit is the identity of product up to isomorphism
⊤-identityˡ : ∀ {A : Set} → ⊤ × A ≃ A
⊤-identityˡ = record
  { to      = λ{ ⟨ tt , x ⟩ → x }
  ; from    = λ{ x → ⟨ tt , x ⟩ }
  ; from∘to = λ{ ⟨ tt , x ⟩ → refl }
  ; to∘from = λ{ x → refl }
  }

⊤-identityʳ : ∀ {A : Set} → A × ⊤ ≃ A
⊤-identityʳ {A} = ≃-begin
  (A × ⊤) ≃⟨ ×-comm ⟩
  (⊤ × A) ≃⟨ ⊤-identityˡ ⟩
  A ≃-∎

-- Disjunction is sum
data _⊎_ (A B : Set) : Set where
  inj₁ : A → A ⊎ B
  inj₂ : B → A ⊎ B

case-⊎ : ∀ {A B C : Set}
  → (A → C)
  → (B → C)
  → A ⊎ B
    -------
  → C
case-⊎ f g (inj₁ x) = f x
case-⊎ f g (inj₂ y) = g y

η-⊎ : ∀ {A B : Set} (w : A ⊎ B) → case-⊎ inj₁ inj₂ w ≡ w
η-⊎ (inj₁ x) = refl
η-⊎ (inj₂ y) = refl

uniq-⊎ : ∀ {A B C : Set} (h : A ⊎ B → C) (w : A ⊎ B) → case-⊎ (h ∘ inj₁) (h ∘ inj₂) w ≡ h w
uniq-⊎ h (inj₁ x) = refl
uniq-⊎ h (inj₂ y) = refl

infixr 1 _⊎_

-- Exercise: ⊎-comm
⊎-comm : ∀ {A B : Set} → A ⊎ B ≃ B ⊎ A
⊎-comm = record
  { to      = λ{ (inj₁ x) → inj₂ x
               ; (inj₂ y) → inj₁ y
               }
  ; from    = λ{ (inj₁ y) → inj₂ y
               ; (inj₂ x) → inj₁ x
               }
  ; from∘to = λ{ (inj₁ x) → refl
               ; (inj₂ y) → refl
               }
  ; to∘from = λ{ (inj₁ y) → refl
               ; (inj₂ x) → refl
               }
  }


-- Exercise ⊎-assoc
⊎-assoc : ∀ {A B C : Set} → A ⊎ (B ⊎ C) ≃ (A ⊎ B) ⊎ C
⊎-assoc = record
  { to      = λ{ (inj₁ x) → inj₁ (inj₁ x)
               ; (inj₂ (inj₁ y)) → inj₁ (inj₂ y)
               ; (inj₂ (inj₂ z)) → inj₂ z
               }
  ; from    = λ{ (inj₁ (inj₁ x)) → inj₁ x
               ; (inj₁ (inj₂ y)) → inj₂ (inj₁ y)
               ; (inj₂ z) → inj₂ (inj₂ z)
               }
  ; from∘to = λ{ (inj₁ x) → refl
               ; (inj₂ (inj₁ y)) → refl
               ; (inj₂ (inj₂ z)) → refl
               }
  ; to∘from = λ{ (inj₁ (inj₁ x)) → refl
               ; (inj₁ (inj₂ y)) → refl
               ; (inj₂ y) → refl
               }
  }

-- False is empty

data ⊥ : Set where
  -- cannot be constructed

⊥-elim : ∀ {A : Set} → ⊥ → A
⊥-elim ()

uniq-⊥ : ∀ {C : Set} (h : ⊥ → C) (w : ⊥) → ⊥-elim w ≡ h w
uniq-⊥ h ()

-- Exercise: ⊥-identityˡ
⊥-identityˡ : ∀ {A : Set} → ⊥ ⊎ A ≃ A
⊥-identityˡ = record
  { to = λ{ (inj₂ x) → x }
  ; from = λ{ x → inj₂ x }
  ; from∘to = λ{ (inj₂ x) → refl }
  ; to∘from = λ{ x → refl }
  }

-- Exercise: ⊥-identityʳ
⊥-identityʳ : ∀ {A : Set} → A ⊎ ⊥ ≃ A
⊥-identityʳ {A} = ≃-begin
  (A ⊎ ⊥) ≃⟨ ⊎-comm ⟩
  (⊥ ⊎ A) ≃⟨ ⊥-identityˡ ⟩
  A ≃-∎

-- Implication is function

→-elim : ∀ {A B : Set}
  → (A → B)
  → A
    -------
  → B
→-elim L M = L M

η-→ : ∀ {A B : Set} (f : A → B) → (λ (x : A) → f x) ≡ f
η-→ f = refl

currying : ∀ {A B C : Set} → (A → B → C) ≃ (A × B → C)
currying = record
  { to      = λ{ f → λ{ ⟨ x , y ⟩ → f x y } }
  ; from    = λ{ g → λ{ x → λ{ y → g ⟨ x , y ⟩ }}}
  ; from∘to = λ{ f → refl }
  ; to∘from = λ{ g → extensionality λ{ ⟨ x , y ⟩ → refl }}
  }

→-distrib-⊎ : ∀ {A B C : Set} → (A ⊎ B → C) ≃ ((A → C) × (B → C))
→-distrib-⊎ = record
  { to      = λ{ f → ⟨ (f ∘ inj₁) , (f ∘ inj₂) ⟩ }
  ; from    = λ{ ⟨ f , g ⟩ → λ{ (inj₁ x) → f x
                              ; (inj₂ y) → g y
                              }}
  ; from∘to = λ{ x → extensionality λ{ (inj₁ x) → refl
                                     ; (inj₂ y) → refl
                                     }}
  ; to∘from = λ{ ⟨ f , g ⟩ → refl }
  }

→-distrib-× : ∀ {A B C : Set} → (A → B × C) ≃ (A → B) × (A → C)
→-distrib-× = record
  { to      = λ{ f → ⟨ proj₁ ∘ f , proj₂ ∘ f ⟩ }
  ; from    = λ{ ⟨ f , g ⟩ → λ{ x → ⟨ f x , g x ⟩ }}
  ; from∘to = λ{ f → extensionality λ{ x → η-× (f x) }}
  ; to∘from = λ{ ⟨ f , g ⟩ → refl }
  }

-- Distribution

×-distrib-⊎ : ∀ {A B C : Set} → (A ⊎ B) × C ≃ (A × C) ⊎ (B × C)
×-distrib-⊎ = record
  { to      = λ{ ⟨ inj₁ x , z ⟩ → inj₁ ⟨ x , z ⟩
               ; ⟨ inj₂ y , z ⟩ → inj₂ ⟨ y , z ⟩
               }
  ; from    = λ{ (inj₁ ⟨ x , z ⟩) → ⟨ inj₁ x , z ⟩
               ; (inj₂ ⟨ y , z ⟩) → ⟨ inj₂ y , z ⟩
               }
  ; from∘to = λ{ ⟨ inj₁ x , z ⟩ → refl
               ; ⟨ inj₂ y , z ⟩ → refl
               }
  ; to∘from = λ{  (inj₁ ⟨ x , z ⟩) → refl
               ;  (inj₂ ⟨ y , z ⟩) → refl
               }
  }

⊎-distrib-× : ∀ {A B C : Set} → (A × B) ⊎ C ≲ (A ⊎ C) × (B ⊎ C)
⊎-distrib-× = record
  { to      = λ{ (inj₁ ⟨ x , y ⟩) → ⟨ inj₁ x , inj₁ y ⟩
               ; (inj₂ z)         → ⟨ inj₂ z , inj₂ z ⟩
               }
  ; from    = λ{ ⟨ inj₁ x , inj₁ y ⟩ → inj₁ ⟨ x , y ⟩
               ; ⟨ inj₁ x , inj₂ z ⟩ → inj₂ z
               ; ⟨ inj₂ z , _      ⟩ → inj₂ z
               }
  ; from∘to = λ{ (inj₁ ⟨ x , y ⟩) → refl
               ; (inj₂ z) → refl
               }
  }

-- Exercise: ⊎-weak-×
⊎-weak-× : ∀ {A B C : Set} → (A ⊎ B) × C → A ⊎ (B × C)
⊎-weak-× = λ{ ⟨ inj₁ x , z ⟩ → inj₁ x
            ; ⟨ inj₂ y , z ⟩ → inj₂ ⟨ y , z ⟩
            }

-- weak law: (A ⊎ B) × C → A ⊎ (B × C)
-- distributive law: (A ⊎ B) × C ≃ (A × C) ⊎ (B × C) ?

-- Exercise: ⊎×-implies-×⊎
⊎×-implies-×⊎ : ∀ {A B C D : Set} → (A × B) ⊎ (C × D) → (A ⊎ C) × (B ⊎ D)
⊎×-implies-×⊎ (inj₁ ⟨ a , b ⟩) = ⟨ inj₁ a , inj₁ b ⟩
⊎×-implies-×⊎ (inj₂ ⟨ c , d ⟩) = ⟨ inj₂ c , inj₂ d ⟩

-- ×⊎-implies-⊎× : ∀ {A B C D : Set} → (A ⊎ C) × (B ⊎ D) → (A × B) ⊎ (C × D)
-- ×⊎-implies-⊎× ⟨ inj₁ a , inj₁ b ⟩ = inj₁ ⟨ a , b ⟩
-- ×⊎-implies-⊎× ⟨ inj₁ a , inj₂ d ⟩ = ?
-- ×⊎-implies-⊎× ⟨ inj₂ c , inj₁ b ⟩ = ?
-- ×⊎-implies-⊎× ⟨ inj₂ c , inj₂ d ⟩ = inj₂ ⟨ c , d ⟩

-- Seems likely the converse doesn't hold... counter example?

-- (a + c) × (b + d) = ab + ad + cb + cd
-- (a × b) + (c × d) = ab + cd
-- Counter example: (⊤ ⊎ ⊥) × (⊤ ⊎ ⊥) does not imply (⊤ × ⊥) ⊎ (⊤ × ⊥)
-- as the second type is uninhabited.
