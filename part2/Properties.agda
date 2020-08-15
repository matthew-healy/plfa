module plfa.part2.Properties where

open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; cong; cong₂)
open import Data.String using (String; _≟_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product
  using (_×_; proj₁; proj₂; ∃; ∃-syntax)
  renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import plfa.part1.Isomorphism
open import plfa.part2.Lambda

-- Values do not reduce
V¬—→ : ∀ {M N}
  → Value M
    ----------
  → ¬ (M —→ N)
V¬—→ (V-suc VM) (ξ-suc M—→N) = V¬—→ VM M—→N

—→¬V : ∀ {M N}
  → M —→ N
    ---------
  → ¬ Value M
—→¬V M—→N VM = V¬—→ VM M—→N

-- Canonical Forms
infix 4 Canonical_⦂_

data Canonical_⦂_ : Term → Type → Set where
  C-ƛ : ∀ {x A N B}
    → ∅ , x ⦂ A ⊢ N ⦂ B
      -----------------------------
    → Canonical (ƛ x ⇒ N) ⦂ (A ⇒ B)

  C-zero :
      --------------------
      Canonical `zero ⦂ `ℕ

  C-suc : ∀ {V}
    → Canonical V ⦂ `ℕ
      ---------------------
    → Canonical `suc V ⦂ `ℕ

-- Every closed, well-typed value is canonical
canonical : ∀ {V A}
  → ∅ ⊢ V ⦂ A
  → Value V
    ---------------
  → Canonical V ⦂ A
canonical (⊢ƛ ⊢N)  V-ƛ         = C-ƛ ⊢N
canonical ⊢zero    V-zero      = C-zero
canonical (⊢suc ⊢V) (V-suc VV) = C-suc (canonical ⊢V VV)

-- If a term is canonical then it is a value
value : ∀ {M A}
  → Canonical M ⦂ A
    ---------------
  → Value M
value (C-ƛ ⊢N)   = V-ƛ
value C-zero     = V-zero
value (C-suc CM) = V-suc (value CM)

-- If a term is canonical then it is well-typed in the empty context
typed : ∀ {M A}
  → Canonical M ⦂ A
    ---------------
  → ∅ ⊢ M ⦂ A
typed (C-ƛ ⊢N)   = ⊢ƛ ⊢N
typed C-zero     = ⊢zero
typed (C-suc CM) = ⊢suc (typed CM)

-- Progress
data Progress (M : Term) : Set where
  step : ∀ {N}
    → M —→ N
      ----------
    → Progress M

  done :
      Value M
      ----------
    → Progress M

progress : ∀ {M A}
  → ∅ ⊢ M ⦂ A
    ----------
  → Progress M
progress (⊢ƛ ⊢N)                            = done V-ƛ
progress (⊢L · ⊢M) with progress ⊢L
... | step L—→L′                            = step (ξ-·₁ L—→L′)
... | done VL with progress ⊢M
...   | step M—→M′                          = step (ξ-·₂ VL M—→M′)
...   | done VM with canonical ⊢L VL
...     | C-ƛ _                             = step (β-ƛ VM)
progress ⊢zero = done V-zero
progress (⊢suc ⊢M) with progress ⊢M
... | step M—→M′                            = step (ξ-suc M—→M′)
... | done VM                               = done (V-suc VM)
progress (⊢case ⊢L ⊢M ⊢N) with progress ⊢L
... | step L—→L′                            = step (ξ-case L—→L′)
... | done VL with canonical ⊢L VL
...   | C-zero                              = step β-zero
...   | C-suc CL                            = step (β-suc (value CL))
progress (⊢μ ⊢M)                            = step β-μ

-- Exercise: Progress-≃
Progress-≃ : ∀ {M : Term} → Progress M ≃ Value M ⊎ ∃[ N ](M —→ N)
Progress-≃ = record
  { to      = to
  ; from    = from
  ; from∘to = from∘to
  ; to∘from = to∘from
  }
  where
  to : ∀ {M : Term} → Progress M → Value M ⊎ ∃[ N ](M —→ N)
  to (step {N} M—→N) = inj₂ ⟨ N , M—→N ⟩
  to (done VM)       = inj₁ VM

  from : ∀ {M : Term} → Value M ⊎ ∃[ N ](M —→ N) → Progress M
  from (inj₁ VM)           = done VM
  from (inj₂ ⟨ N , M—→N ⟩) = step M—→N

  from∘to : ∀ {M : Term} (PM : Progress M) → from (to PM) ≡ PM
  from∘to (step M—→N) = refl
  from∘to (done VM)   = refl

  to∘from : ∀ {M : Term} (OM : Value M ⊎ ∃[ N ](M —→ N)) → to (from OM) ≡ OM
  to∘from (inj₁ VM) = refl
  to∘from (inj₂ ∃M) = refl

-- Exercise: progress′
progress′ : ∀ M {A} → ∅ ⊢ M ⦂ A → Value M ⊎ ∃[ N ](M —→ N)
progress′ (` x) (⊢` ())
progress′ (ƛ x ⇒ M) ⊢ƛx⇒M    = inj₁ V-ƛ
progress′ (L · M) (⊢L · ⊢M) with progress′ L ⊢L
... | inj₂ ⟨ L′ , L—→L′ ⟩    = inj₂ ⟨ L′ · M , ξ-·₁ L—→L′ ⟩
... | inj₁ VL with progress′ M ⊢M
...   | inj₂ ⟨ M′ , M—→M′ ⟩  = inj₂ ⟨ L · M′ , ξ-·₂ VL M—→M′ ⟩
...   | inj₁ VM with canonical ⊢L VL
...     | C-ƛ {x} {N = N} ⊢N = inj₂ ⟨ N [ x := M ] , β-ƛ VM ⟩
progress′ `zero ⊢M = inj₁ V-zero
progress′ (`suc M) (⊢suc ⊢M) with progress′ M ⊢M
... | inj₂ ⟨ N , M—→N ⟩      = inj₂ ⟨ `suc N , ξ-suc M—→N ⟩
... | inj₁ VM                = inj₁ (V-suc VM)
progress′ case L [zero⇒ M |suc x ⇒ N ] (⊢case ⊢L ⊢M ⊢N) with progress′ L ⊢L
... | inj₂ ⟨ L′ , L—→L′ ⟩    = inj₂ ⟨ case L′ [zero⇒ M |suc x ⇒ N ] , ξ-case L—→L′ ⟩
... | inj₁ VL with canonical ⊢L VL
...   | C-zero               = inj₂ ⟨ M , β-zero ⟩
...   | C-suc {V} CL         = inj₂ ⟨ N [ x := V ] , β-suc (value CL)  ⟩
progress′ (μ x ⇒ M) (⊢μ ⊢M) = inj₂ ⟨ M [ x := μ x ⇒ M ] , β-μ ⟩

-- Exercise: value?
value? : ∀ {A M} → ∅ ⊢ M ⦂ A → Dec (Value M)
value? ⊢M with progress ⊢M
... | step M—→M′ = no (—→¬V M—→M′)
... | done VM = yes VM
