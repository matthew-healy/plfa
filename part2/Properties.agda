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

-- Prelude to Preservation: Renaming

ext : ∀ {Γ Δ}
  → (∀ {x A}     →         Γ ∋ x ⦂ A →        Δ ∋ x ⦂ A) -- if x has the same type in both contexts
    ---------------------------------------------------
  → (∀ {x y A B} → Γ , y ⦂ B ∋ x ⦂ A → Δ , y ⦂ B ∋ x ⦂ A) -- then it has the same type in extensions of those contexts
ext ρ Z        = Z
ext ρ (S x≢y ∋x) = S x≢y (ρ ∋x)

rename : ∀ {Γ Δ}
  → (∀ {x A} → Γ ∋ x ⦂ A → Δ ∋ x ⦂ A)
    --------------------------------
  → (∀ {M A} → Γ ⊢ M ⦂ A → Δ ⊢ M ⦂ A)
rename ρ (⊢` ∋w)          = ⊢` (ρ ∋w)
rename ρ (⊢ƛ ⊢N)          = ⊢ƛ (rename (ext ρ) ⊢N)
rename ρ (⊢L · ⊢M)        = (rename ρ ⊢L) · (rename ρ ⊢M)
rename ρ ⊢zero            = ⊢zero
rename ρ (⊢suc ⊢M)        = ⊢suc (rename ρ ⊢M)
rename ρ (⊢case ⊢L ⊢M ⊢N) = ⊢case (rename ρ ⊢L) (rename ρ ⊢M) (rename (ext ρ) ⊢N)
rename ρ (⊢μ ⊢M)          = ⊢μ (rename (ext ρ) ⊢M)

weaken : ∀ {Γ M A} -- A closed term can be weakened to any context
  → ∅ ⊢ M ⦂ A
    ---------
  → Γ ⊢ M ⦂ A
weaken {Γ} ⊢M = rename ρ ⊢M
  where
  ρ : ∀ {z C}
    → ∅ ∋ z ⦂ C
      ---------
    → Γ ∋ z ⦂ C
  ρ ()

drop : ∀ {Γ x M A B C} -- If the last two variables in any context have the same name then we can drop the shadowed one.
  → Γ , x ⦂ A , x ⦂ B ⊢ M ⦂ C
    ------------------------
  → Γ , x ⦂ B ⊢ M ⦂ C
drop {Γ} {x} {M} {A} {B} ⊢M = rename ρ ⊢M
  where
  ρ : ∀ {z C}
    → Γ , x ⦂ A , x ⦂ B ∋ z ⦂ C
      ------------------------
    → Γ , x ⦂ B ∋ z ⦂ C
  ρ Z                = Z
  ρ (S x≢x Z)        = ⊥-elim (x≢x refl)
  ρ (S z≢x (S _ ∋z)) = S z≢x ∋z

swap : ∀ {Γ x y M A B C} -- If the last two variables in any context have different names then we can swap them.
  → x ≢ y
  → Γ , y ⦂ B , x ⦂ A ⊢ M ⦂ C
    ------------------------
  → Γ , x ⦂ A , y ⦂ B ⊢ M ⦂ C
swap {Γ} {x} {y} {M} {A} {B} x≢y ⊢M = rename ρ ⊢M
  where
  ρ : ∀ {z C}
    → Γ , y ⦂ B , x ⦂ A ∋ z ⦂ C
      ------------------------
    → Γ , x ⦂ A , y ⦂ B ∋ z ⦂ C
  ρ Z                  = S x≢y Z
  ρ (S z≢x Z)          = Z
  ρ (S z≢x (S z≢y ∋z)) = S z≢y (S z≢x ∋z)

-- Prelude to Preservation: Substitution

subst : ∀ {Γ x N V A B}
  → ∅ ⊢ V ⦂ A
  → Γ , x ⦂ A ⊢ N ⦂ B
    --------------------
  → Γ ⊢ N [ x := V ] ⦂ B
subst {x = y} ⊢V (⊢` {x = x} Z) with x ≟ y
... | yes _           = weaken ⊢V
... | no  x≢y         = ⊥-elim (x≢y refl)
subst {x = y} ⊢V (⊢` {x = x} (S x≢y ∋x)) with x ≟ y
... | yes refl        = ⊥-elim (x≢y refl)
... | no  _           = ⊢` ∋x
subst {x = y} ⊢V (⊢ƛ {x = x} ⊢N) with x ≟ y
... | yes refl        = ⊢ƛ (drop ⊢N)
... | no x≢y          = ⊢ƛ (subst ⊢V (swap x≢y ⊢N))
subst ⊢V (⊢L · ⊢M)   = (subst ⊢V ⊢L) · (subst ⊢V ⊢M)
subst ⊢V ⊢zero       = ⊢zero
subst ⊢V (⊢suc ⊢N)   = ⊢suc (subst ⊢V ⊢N)
subst {x = y} ⊢V (⊢case {x = x} ⊢L ⊢M ⊢N) with x ≟ y
... | yes refl       = ⊢case (subst ⊢V ⊢L) (subst ⊢V ⊢M) (drop ⊢N)
... | no x≢y         = ⊢case (subst ⊢V ⊢L) (subst ⊢V ⊢M) (subst ⊢V (swap x≢y ⊢N))
subst {x = y} ⊢V (⊢μ {x = x} ⊢M) with x ≟ y
... | yes refl       = ⊢μ (drop ⊢M)
... | no x≢y         = ⊢μ (subst ⊢V (swap x≢y ⊢M))

-- Exercise: subst′
subst′ : ∀ {Γ x N V A B}
  → ∅ ⊢ V ⦂ A
  → Γ , x ⦂ A ⊢ N ⦂ B
    --------------------
  → Γ ⊢ N [ x := V ]′ ⦂ B

-- lol wtf
subst-subterm : ∀ {x y : Id} → ∀ {Γ f N V A B C D}
  → ∅ ⊢ V ⦂ A
  → Γ , y ⦂ A , x ⦂ B ⊢ N ⦂ C
  → (∀ {P} → Γ , x ⦂ B ⊢ P ⦂ C → Γ ⊢ f P ⦂ D)
    -----------------------------------------
  → Γ ⊢ replaceIfNotEqual x y f N V ⦂ D

-- These remain the same
subst′ {x = y} ⊢V (⊢` {x = x} Z) with x ≟ y
... | yes _   = weaken ⊢V
... | no  x≢y = ⊥-elim (x≢y refl)
subst′ {x = y} ⊢V (⊢` {x = x} (S x≢y ∋x)) with x ≟ y
... | yes refl = ⊥-elim (x≢y refl)
... | no  _    = ⊢` ∋x
subst′ ⊢V (⊢L · ⊢M) = (subst′ ⊢V ⊢L) · (subst′ ⊢V ⊢M)
subst′ ⊢V ⊢zero     = ⊢zero
subst′ ⊢V (⊢suc ⊢N) = ⊢suc (subst′ ⊢V ⊢N)

subst′ ⊢V (⊢ƛ ⊢N)          = subst-subterm ⊢V ⊢N λ{ P → ⊢ƛ P }
subst′ ⊢V (⊢case ⊢L ⊢M ⊢N) = subst-subterm ⊢V ⊢N λ{ P → ⊢case (subst′ ⊢V ⊢L) (subst′ ⊢V ⊢M) P }
subst′ ⊢V (⊢μ ⊢N)          = subst-subterm ⊢V ⊢N λ{ P → ⊢μ P }

subst-subterm {x} {y} ⊢V ⊢N g with x ≟ y
... | yes refl = g (drop ⊢N)
... | no  x≢y  = g (subst′ ⊢V (swap x≢y ⊢N))

-- Preservation
preserve : ∀ {M N A}
  → ∅ ⊢ M ⦂ A
  → M —→ N
    ---------
  → ∅ ⊢ N ⦂ A
preserve (⊢L · ⊢M)               (ξ-·₁ L—→L′)    = (preserve ⊢L L—→L′) · ⊢M
preserve (⊢L · ⊢M)               (ξ-·₂ VL M—→M′) = ⊢L · (preserve ⊢M M—→M′)
preserve ((⊢ƛ ⊢N) · ⊢V)          (β-ƛ VV)        = subst ⊢V ⊢N
preserve (⊢suc ⊢M)               (ξ-suc M—→M′)   = ⊢suc (preserve ⊢M M—→M′)
preserve (⊢case ⊢L ⊢M ⊢N)        (ξ-case L—→L′)  = ⊢case (preserve ⊢L L—→L′) ⊢M ⊢N
preserve (⊢case ⊢L ⊢M ⊢N)        β-zero          = ⊢M
preserve (⊢case (⊢suc ⊢V) ⊢M ⊢N) (β-suc VV)      = subst ⊢V ⊢N
preserve (⊢μ ⊢M)                 β-μ             = subst (⊢μ ⊢M) ⊢M
