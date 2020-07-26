module plfa.part1.Negation where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import plfa.part1.Isomorphism using (_≃_; _≲_; extensionality)
open import plfa.part1.Relations using (_<_; z<s; s<s)

-- Negation

¬_ : Set → Set
¬ A = A → ⊥

¬-elim : ∀ {A : Set} → ¬ A → A → ⊥
¬-elim ¬x x = ¬x x

infix 3 ¬_

¬¬-intro : ∀ {A : Set} → A → ¬ ¬ A
¬¬-intro x = λ{ ¬x → ¬x x }

¬¬-intro′ : ∀ {A : Set} → A → ¬ ¬ A
¬¬-intro′ x ¬x = ¬x x

¬¬¬-elim : ∀ {A : Set} → ¬ ¬ ¬ A → ¬ A
¬¬¬-elim ¬¬¬x = λ{ x → ¬¬¬x (¬¬-intro x) }

contraposition : ∀ {A B : Set} → (A → B) → (¬ B → ¬ A)
contraposition f ¬y x = ¬y (f x)

_≢_ : ∀ {A : Set} → A → A → Set
x ≢ y = ¬ (x ≡ y)

_ : 1 ≢ 2
_ = λ()

peano : ∀ {m : ℕ} → zero ≢ suc m
peano = λ()

-- One proof of ⊥ → ⊥

id : ⊥ → ⊥
id x = x

id′ : ⊥ → ⊥
id′ ()

id≡id′ : id ≡ id′
id≡id′ = extensionality (λ())

-- Can show any two proofs of a negation are equal:
assimilation : ∀ {A : Set} (¬x ¬x′ : ¬ A) → ¬x ≡ ¬x′
assimilation ¬x ¬x′ = extensionality (λ x → ⊥-elim (¬x x))


-- Exercise: <-irreflexive
<-irreflexive : ∀ (n : ℕ) → ¬ (n < n)
<-irreflexive zero = λ()
<-irreflexive (suc n) = λ{ (_<_.s<s n<n) → (<-irreflexive n) n<n }

-- Exercise: Trichotomy
-- This proof could/should probably be made more readable (with where clauses?).
trichotomy : ∀ (m n : ℕ)
  → (m < n × m ≢ n × ¬ n < m)
  ⊎ (¬ m < n × m ≡ n × ¬ n < m)
  ⊎ (¬ m < n × m ≢ n × n < m)
trichotomy zero zero = inj₂ (inj₁ ((λ()) , refl , λ()))
trichotomy zero (suc n) = inj₁ (z<s , (λ()) , (λ()) )
trichotomy (suc m) zero = inj₂ (inj₂ ((λ()) , (λ()) , z<s))
trichotomy (suc m) (suc n) with trichotomy m n
...                           | inj₁ (m<n , m≢n , ¬n<m)
                                 = inj₁ (
                                    s<s m<n ,
                                    (λ{refl → m≢n refl}) ,
                                    λ{(s<s n<m) → ¬n<m n<m}
                                  )
...                           | inj₂ (inj₁ (¬m<n , m≡n , ¬n<m))
                                = inj₂ (inj₁ (
                                    (λ{(s<s m<n) → ¬m<n m<n}) ,
                                    cong suc m≡n ,
                                    λ{(s<s n<m) → ¬n<m n<m}
                                  ))
...                           | inj₂ (inj₂ (¬m<n , m≢n , n<m))
                                = inj₂ (inj₂ ((
                                    λ{(s<s m<n) → ¬m<n m<n}) ,
                                    (λ{refl → m≢n refl}) ,
                                    s<s n<m
                                  ))

-- Exercise: ⊎-dual-×
-- Reproving this using stdlib types since the version in Connectives using
-- the handwritten ones.
→-distrib-⊎ : ∀ {A B C : Set} → (A ⊎ B → C) ≃ ((A → C) × (B → C))
→-distrib-⊎ = record
  { to      = λ{ A⊎B→C → (λ x → A⊎B→C (inj₁ x)) , λ y → A⊎B→C (inj₂ y) }
  ; from    = λ{ [A→C]×[B→C] (inj₁ x) → proj₁ [A→C]×[B→C] x
               ; [A→C]×[B→C] (inj₂ y) → proj₂ [A→C]×[B→C] y
               }
  ; from∘to = λ{ A⊎B→C → extensionality (λ{ (inj₁ x) → refl
                                          ; (inj₂ y) → refl })
                                          }
  ; to∘from = λ{ [A→C]×[B→C] → refl }
  }

demorgan : ∀ {A B : Set} → ¬ (A ⊎ B) ≃ (¬ A) × (¬ B)
demorgan = →-distrib-⊎ {_} {_} {⊥}

-- Do we also have ¬(A × B) ≃ (¬ A) ⊎ (¬ B)?
-- ⊎ is xor, so does not encode the possibility that A and B might both be false.
-- whereas × is and, so ¬[A×B] implies either ¬A, ¬B or both.
-- This prevents us from implementing from : ¬(A × B) → (¬ A) ⊎ (¬ B

-- Can prove: (¬ A) ⊎ (¬ B) → ¬(A × B)
_ : ∀ {A B : Set} → (¬ A) ⊎ (¬ B) → ¬(A × B)
_ = λ{ (inj₁ ¬A) (x , y) → ¬A x
     ; (inj₂ ¬B) (x , y) → ¬B y
     }
