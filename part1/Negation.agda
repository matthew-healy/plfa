module plfa.part1.Negation where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂; swap)
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
-- This prevents us from implementing from : ¬(A × B) → (¬ A) ⊎ (¬ B)

-- Can prove: (¬ A) ⊎ (¬ B) → ¬(A × B)
_ : ∀ {A B : Set} → (¬ A) ⊎ (¬ B) → ¬(A × B)
_ = λ{ (inj₁ ¬A) (x , y) → ¬A x
     ; (inj₂ ¬B) (x , y) → ¬B y
     }

-- Excluded middle is irrefutable
postulate
  em : ∀ {A : Set} → A ⊎ ¬ A

em-irrefutable : ∀ {A : Set} → ¬ ¬ (A ⊎ ¬ A)
em-irrefutable k = k (inj₂ λ{ x → k (inj₁ x) })

-- Exercise: Classical

-- Excluded middle → others
em→dne : ∀ {A : Set} → A ⊎ ¬ A → (¬ ¬ A → A)
em→dne (inj₁ x) ¬¬A = x
em→dne (inj₂ y) ¬¬A = ⊥-elim (¬¬A y)

em→pl : ∀ {A B : Set} → A ⊎ ¬ A → ((A → B) → A) → A
em→pl (inj₁ x) [A→B]→A = x
em→pl (inj₂ y) [A→B]→A = [A→B]→A λ{ x → ⊥-elim (y x) }

em→iad : ∀ {A B : Set} → A ⊎ ¬ A → (A → B) → ¬ A ⊎ B
em→iad (inj₁ a) A→B = inj₂ (A→B a)
em→iad (inj₂ ¬a) A→B = inj₁ ¬a

em→dm : (∀ {A : Set} → A ⊎ ¬ A) → ∀ {A B : Set} → ¬(¬ A × ¬ B) → A ⊎ B
em→dm lem {A} {B} ¬[¬A×¬B] with lem {A} | lem {B}
...                           | inj₁ x  |    y⊎¬y = inj₁ x
...                           | inj₂ ¬x | inj₁  y = inj₂ y
...                           | inj₂ ¬x | inj₂ ¬y = ⊥-elim (¬[¬A×¬B] (¬x , ¬y))

-- Double negation elimination → others
dne→em : (∀ {A : Set} → ¬ ¬ A → A) → ∀ {A : Set} → A ⊎ ¬ A
dne→em ¬¬A→A = ¬¬A→A em-irrefutable

-- Since em→ all others, and dne→em, we get that dne→ all the others

dne→pl : (∀ {A : Set} → ¬ ¬ A → A) → ∀ {A B : Set} → ((A → B) → A) → A
dne→pl ¬¬A→A [A→B]→A = em→pl (dne→em ¬¬A→A) [A→B]→A

dne→iad : (∀ {A : Set} → ¬ ¬ A → A) → ∀ {A B : Set} → (A → B) → ¬ A ⊎ B
dne→iad ¬¬A→A A→B = em→iad (dne→em ¬¬A→A) A→B

dne→dm : (∀ {A : Set} → ¬ ¬ A → A) → ∀ {A B : Set} → ¬(¬ A × ¬ B) → A ⊎ B
dne→dm ¬¬A→A ¬[¬A×¬B] = em→dm (dne→em ¬¬A→A) ¬[¬A×¬B]

-- Pierce's law → others
pl→em : (∀ {A : Set} → ¬ ¬ A → A) → ∀ {A : Set} → A ⊎ ¬ A
pl→em ¬¬A→A = ¬¬A→A λ{ ¬[A⊎¬A] → ⊥-elim (em-irrefutable ¬[A⊎¬A]) }

pl→dne : (∀ {A : Set} → ¬ ¬ A → A) → ∀ {A : Set} → (¬ ¬ A → A)
pl→dne ¬¬A→A = em→dne (pl→em ¬¬A→A)

pl→iad : (∀ {A : Set} → ¬ ¬ A → A) → ∀ {A B : Set} → (A → B) → ¬ A ⊎ B
pl→iad ¬¬A→A A→B = em→iad (pl→em ¬¬A→A) A→B

pl→dm : (∀ {A : Set} → ¬ ¬ A → A) → ∀ {A B : Set} → ¬(¬ A × ¬ B) → A ⊎ B
pl→dm ¬¬A→A ¬[¬A×¬B] = em→dm (pl→em ¬¬A→A) ¬[¬A×¬B]

-- Implication as disjunction → others

iad→em : (∀ {A B : Set} → (A → B) → ¬ A ⊎ B) → ∀ {A : Set} → A ⊎ ¬ A
iad→em iad = swap (iad λ{ x → x })

-- em → all others, so we're done.

-- DeMorgan's law → others

dm→em : (∀ {A B : Set} → ¬(¬ A × ¬ B) → A ⊎ B) → ∀ {A : Set} → A ⊎ ¬ A
dm→em dm = dm λ{ (¬a , ¬¬a) → ¬¬a ¬a }

-- em → all others, so done

-- Exercise: Stable

Stable : Set → Set
Stable A = ¬ ¬ A → A

¬-stable : ∀ {A : Set} → Stable (¬ A)
¬-stable = ¬¬¬-elim

×-stable : ∀ {A B : Set} → Stable A → Stable B → Stable (A × B)
×-stable ¬¬x→x ¬¬y→y ¬¬[A×B] =
  (¬¬x→x λ{ ¬x → ¬¬[A×B] λ { xy → ¬x (proj₁ xy) }}) ,
  (¬¬y→y λ{ ¬y → ¬¬[A×B] λ { xy → ¬y (proj₂ xy) }})
