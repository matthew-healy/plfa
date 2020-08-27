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

-- Evaluation

record Gas : Set where
  constructor gas
  field
    amount : ℕ

data Finished (N : Term) : Set where
  done :
      Value N
      ----------
    → Finished N

  out-of-gas :
      ----------
      Finished N

data Steps (L : Term) : Set where
  steps : ∀ {N}
    → L —↠ N
    → Finished N
      ----------
    → Steps L

eval : ∀ {L A}
  → Gas
  → ∅ ⊢ L ⦂ A
    ---------
  → Steps L
eval {L} (gas zero)    ⊢L = steps (L ∎) out-of-gas
eval {L} (gas (suc m)) ⊢L with progress ⊢L
... | done VL             = steps (L ∎) (done VL)
... | step {M} L—→M with eval (gas m) (preserve ⊢L L—→M)
...   | steps M—↠N fin    = steps (L —→⟨ L—→M ⟩ M—↠N) fin

-- Examples
⊢sucμ : ∅ ⊢ μ "x" ⇒ `suc ` "x" ⦂ `ℕ
⊢sucμ = ⊢μ (⊢suc (⊢` ∋x))
  where
  ∋x = Z

_ : eval (gas 3) ⊢sucμ ≡
  steps
  (μ "x" ⇒ `suc ` "x"
  —→⟨ β-μ ⟩
  `suc (μ "x" ⇒ `suc ` "x")
  —→⟨ ξ-suc β-μ ⟩
  `suc (`suc (μ "x" ⇒ `suc ` "x"))
  —→⟨ ξ-suc (ξ-suc β-μ) ⟩
  `suc (`suc (`suc (μ "x" ⇒ `suc ` "x")))
  ∎)
  out-of-gas
_ = refl

-- Exercise: mul-eval
-- See the end of this doc. It is _long_.

-- Exercise: progress-preservation

-- Progress: Every closed, well-typed term either is a value or can be reduced.
-- Preservation: If a closed, well-typed term reduces, then the term it reduces to is also closed and well-typed.
-- (I had to look these up because it's been a while since I started this chapter and also I'm an awful cheater.)

-- Exercise: subject-expansion
-- case example:
-- `zero expands to case `zero [zero⇒ `zero |suc "m" ⇒ ` "n" ]
-- but the latter is not closed or well-typed.
-- non-case example:
-- Let I be the term ƛ "x" ⇒ ` "x"
-- and let K be the term ƛ "x" ⇒ ƛ "y" ⇒ ` "x"
-- then I expands to K · I · ` "m" which is not closed or well-typed.

-- Well-typed terms don't get stuck

Normal : Term → Set
Normal M = ∀ {N} → ¬ (M —→ N)

Stuck : Term → Set
Stuck M = Normal M × ¬ Value M

unstuck : ∀ {M A}
  → ∅ ⊢ M ⦂ A
    -----------
  → ¬ (Stuck M)
unstuck ⊢M ⟨ NM , ¬VM ⟩ with progress ⊢M
... | step M—→N = NM M—→N
... | done VM   = ¬VM VM

preserves : ∀ {M N A}
  → ∅ ⊢ M ⦂ A
  → M —↠ N
    ---------
  → ∅ ⊢ N ⦂ A
preserves ⊢M (M ∎) = ⊢M
preserves ⊢M (M —→⟨ M—→L ⟩ L—↠N) with preserve ⊢M M—→L
... | ⊢L = preserves ⊢L L—↠N

wttdgs : ∀ {M N A}
  → ∅ ⊢ M ⦂ A
  → M —↠ N
    -----------
  → ¬ (Stuck N)
wttdgs ⊢M M—↠N SN = unstuck (preserves ⊢M M—↠N) SN

-- Exercise: stuck
-- `zero · `zero
-- is ill-typed and stuck.

-- Exercise: unstuck
-- See above.

-- Exercise: mul-eval
-- ⊢2*2 : ∅ ⊢ mul · two · two ⦂ `ℕ
-- ⊢2*2 = ⊢mul · ⊢two · ⊢two

-- Reduction is deterministic
cong₄ : ∀ {A B C D E : Set} (f : A → B → C → D → E)
  {s w : A} {t x : B} {u y : C} {v z : D}
  → s ≡ w → t ≡ x → u ≡ y → v ≡ z → f s t u v ≡ f w x y z
cong₄ f refl refl refl refl = refl

det : ∀ {M M′ M″}
  → (M —→ M′)
  → (M —→ M″)
    ---------
  → M′ ≡ M″
det (ξ-·₁ L—→L′)    (ξ-·₁ L—→L″)    = cong₂ _·_ (det L—→L′ L—→L″) refl
det (ξ-·₁ L—→L′)    (ξ-·₂ VL M—→M″) = ⊥-elim (V¬—→ VL L—→L′)
det (ξ-·₂ VL M—→M′) (ξ-·₁ L—→L″)    = ⊥-elim (V¬—→ VL L—→L″)
det (ξ-·₂ _ M—→M′)  (ξ-·₂ _ M—→M″)  = cong₂ _·_ refl (det M—→M′ M—→M″)
det (ξ-·₂ _ M—→M′)  (β-ƛ VM)        = ⊥-elim (V¬—→ VM M—→M′)
det (β-ƛ VM)        (ξ-·₂ _ M—→M″)  = ⊥-elim (V¬—→ VM M—→M″)
det (β-ƛ _)         (β-ƛ _)         = refl
det (ξ-suc M—→M′)   (ξ-suc M—→M″)   = cong `suc_ (det M—→M′ M—→M″)
det (ξ-case L—→L′)  (ξ-case L—→L″)  = cong₄ case_[zero⇒_|suc_⇒_]
                                        (det L—→L′ L—→L″) refl refl refl
det (ξ-case L—→L′)  (β-suc VL)      = ⊥-elim (V¬—→ (V-suc VL) L—→L′)
det β-zero          β-zero          = refl
det (β-suc VL)      (ξ-case L—→L″)  = ⊥-elim (V¬—→ (V-suc VL) L—→L″)
det (β-suc _)       (β-suc _)       = refl
det β-μ             β-μ             = refl

-- Quiz: zap

-- Determinism of step: becomes false.
--   Example: Say M —→ M′ where M′ is not zap. By β-zap we have M —→ zap also.
-- Progress: remains true if zap is a value. Otherwise false as zap itself doesn't step to anything.
-- Preservation: remains true.

-- Quiz: foo

-- Determinism of step: remains true.
-- Progress: remains true.
-- Preservation: becomes false.
--   Example: (ƛ "x" ⇒ ` "x") has type A ⇒ A for any A, but it reduces to foo
--   and then foo reduces to `zero which has type `ℕ, so the type is not preserved.

-- Quiz: removing ξ·₁

-- Determinism of step: remains true.
-- Progress: does not hold.
--   Example: ((ƛ "x" ⇒ `"x") · (ƛ "x" ⇒ ` "x")) · `zero cannot step without ξ·₁.
-- Preservation: remains true.

-- Quiz: ·ℕ

-- N.b. this is largely a guess, as I didn't try to actually implement this.
-- However, it seems to be related to the concept of δ-reduction, which simply
-- lets us replace predefined functions with their known numerical results as
-- part of typechecking. I couldn't find anything that suggested this would
-- cause any issues with the properties we already proved for the simply typed
-- lambda calculus.

-- Determinism of step: remains true.
-- Progress: remains true.
-- Preservation: remains true.

-- Exercise: mul-eval solution from above

-- mul-eval : eval (gas 100) ⊢2*2 ≡
--   steps
--   ((μ "×" ⇒
--   (ƛ "m" ⇒
--    (ƛ "n" ⇒
--     case ` "m" [zero⇒ `zero |suc "m" ⇒
--     (μ "+" ⇒
--      (ƛ "m" ⇒
--       (ƛ "n" ⇒
--        case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
--        ])))
--     · ` "n"
--     · (` "×" · ` "m" · ` "n")
--     ])))
--   · `suc (`suc `zero)
--   · `suc (`suc `zero)
--   —→⟨ ξ-·₁ (ξ-·₁ β-μ) ⟩
--   (ƛ "m" ⇒
--   (ƛ "n" ⇒
--    case ` "m" [zero⇒ `zero |suc "m" ⇒
--    (μ "+" ⇒
--     (ƛ "m" ⇒
--      (ƛ "n" ⇒
--       case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
--       ])))
--    · ` "n"
--    ·
--    ((μ "×" ⇒
--      (ƛ "m" ⇒
--       (ƛ "n" ⇒
--        case ` "m" [zero⇒ `zero |suc "m" ⇒
--        (μ "+" ⇒
--         (ƛ "m" ⇒
--          (ƛ "n" ⇒
--           case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
--           ])))
--        · ` "n"
--        · (` "×" · ` "m" · ` "n")
--        ])))
--     · ` "m"
--     · ` "n")
--    ]))
--   · `suc (`suc `zero)
--   · `suc (`suc `zero)
--   —→⟨ ξ-·₁ (β-ƛ (V-suc (V-suc V-zero))) ⟩
--   (ƛ "n" ⇒
--   case `suc (`suc `zero) [zero⇒ `zero |suc "m" ⇒
--   (μ "+" ⇒
--    (ƛ "m" ⇒
--     (ƛ "n" ⇒
--      case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
--      ])))
--   · ` "n"
--   ·
--   ((μ "×" ⇒
--     (ƛ "m" ⇒
--      (ƛ "n" ⇒
--       case ` "m" [zero⇒ `zero |suc "m" ⇒
--       (μ "+" ⇒
--        (ƛ "m" ⇒
--         (ƛ "n" ⇒
--          case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
--          ])))
--       · ` "n"
--       · (` "×" · ` "m" · ` "n")
--       ])))
--    · ` "m"
--    · ` "n")
--   ])
--   · `suc (`suc `zero)
--   —→⟨ β-ƛ (V-suc (V-suc V-zero)) ⟩
--   case `suc (`suc `zero) [zero⇒ `zero |suc "m" ⇒
--   (μ "+" ⇒
--   (ƛ "m" ⇒
--    (ƛ "n" ⇒
--     case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
--     ])))
--   · `suc (`suc `zero)
--   ·
--   ((μ "×" ⇒
--    (ƛ "m" ⇒
--     (ƛ "n" ⇒
--      case ` "m" [zero⇒ `zero |suc "m" ⇒
--      (μ "+" ⇒
--       (ƛ "m" ⇒
--        (ƛ "n" ⇒
--         case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
--         ])))
--      · ` "n"
--      · (` "×" · ` "m" · ` "n")
--      ])))
--   · ` "m"
--   · `suc (`suc `zero))
--   ]
--   —→⟨ β-suc (V-suc V-zero) ⟩
--   (μ "+" ⇒
--   (ƛ "m" ⇒
--    (ƛ "n" ⇒
--     case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
--     ])))
--   · `suc (`suc `zero)
--   ·
--   ((μ "×" ⇒
--    (ƛ "m" ⇒
--     (ƛ "n" ⇒
--      case ` "m" [zero⇒ `zero |suc "m" ⇒
--      (μ "+" ⇒
--       (ƛ "m" ⇒
--        (ƛ "n" ⇒
--         case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
--         ])))
--      · ` "n"
--      · (` "×" · ` "m" · ` "n")
--      ])))
--   · `suc `zero
--   · `suc (`suc `zero))
--   —→⟨ ξ-·₁ (ξ-·₁ β-μ) ⟩
--   (ƛ "m" ⇒
--   (ƛ "n" ⇒
--    case ` "m" [zero⇒ ` "n" |suc "m" ⇒
--    `suc
--    ((μ "+" ⇒
--      (ƛ "m" ⇒
--       (ƛ "n" ⇒
--        case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
--        ])))
--     · ` "m"
--     · ` "n")
--    ]))
--   · `suc (`suc `zero)
--   ·
--   ((μ "×" ⇒
--    (ƛ "m" ⇒
--     (ƛ "n" ⇒
--      case ` "m" [zero⇒ `zero |suc "m" ⇒
--      (μ "+" ⇒
--       (ƛ "m" ⇒
--        (ƛ "n" ⇒
--         case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
--         ])))
--      · ` "n"
--      · (` "×" · ` "m" · ` "n")
--      ])))
--   · `suc `zero
--   · `suc (`suc `zero))
--   —→⟨ ξ-·₁ (β-ƛ (V-suc (V-suc V-zero))) ⟩
--   (ƛ "n" ⇒
--   case `suc (`suc `zero) [zero⇒ ` "n" |suc "m" ⇒
--   `suc
--   ((μ "+" ⇒
--     (ƛ "m" ⇒
--      (ƛ "n" ⇒
--       case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
--       ])))
--    · ` "m"
--    · ` "n")
--   ])
--   ·
--   ((μ "×" ⇒
--    (ƛ "m" ⇒
--     (ƛ "n" ⇒
--      case ` "m" [zero⇒ `zero |suc "m" ⇒
--      (μ "+" ⇒
--       (ƛ "m" ⇒
--        (ƛ "n" ⇒
--         case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
--         ])))
--      · ` "n"
--      · (` "×" · ` "m" · ` "n")
--      ])))
--   · `suc `zero
--   · `suc (`suc `zero))
--   —→⟨ ξ-·₂ V-ƛ (ξ-·₁ (ξ-·₁ β-μ)) ⟩
--   (ƛ "n" ⇒
--   case `suc (`suc `zero) [zero⇒ ` "n" |suc "m" ⇒
--   `suc
--   ((μ "+" ⇒
--     (ƛ "m" ⇒
--      (ƛ "n" ⇒
--       case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
--       ])))
--    · ` "m"
--    · ` "n")
--   ])
--   ·
--   ((ƛ "m" ⇒
--    (ƛ "n" ⇒
--     case ` "m" [zero⇒ `zero |suc "m" ⇒
--     (μ "+" ⇒
--      (ƛ "m" ⇒
--       (ƛ "n" ⇒
--        case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
--        ])))
--     · ` "n"
--     ·
--     ((μ "×" ⇒
--       (ƛ "m" ⇒
--        (ƛ "n" ⇒
--         case ` "m" [zero⇒ `zero |suc "m" ⇒
--         (μ "+" ⇒
--          (ƛ "m" ⇒
--           (ƛ "n" ⇒
--            case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
--            ])))
--         · ` "n"
--         · (` "×" · ` "m" · ` "n")
--         ])))
--      · ` "m"
--      · ` "n")
--     ]))
--   · `suc `zero
--   · `suc (`suc `zero))
--   —→⟨ ξ-·₂ V-ƛ (ξ-·₁ (β-ƛ (V-suc V-zero))) ⟩
--   (ƛ "n" ⇒
--   case `suc (`suc `zero) [zero⇒ ` "n" |suc "m" ⇒
--   `suc
--   ((μ "+" ⇒
--     (ƛ "m" ⇒
--      (ƛ "n" ⇒
--       case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
--       ])))
--    · ` "m"
--    · ` "n")
--   ])
--   ·
--   ((ƛ "n" ⇒
--    case `suc `zero [zero⇒ `zero |suc "m" ⇒
--    (μ "+" ⇒
--     (ƛ "m" ⇒
--      (ƛ "n" ⇒
--       case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
--       ])))
--    · ` "n"
--    ·
--    ((μ "×" ⇒
--      (ƛ "m" ⇒
--       (ƛ "n" ⇒
--        case ` "m" [zero⇒ `zero |suc "m" ⇒
--        (μ "+" ⇒
--         (ƛ "m" ⇒
--          (ƛ "n" ⇒
--           case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
--           ])))
--        · ` "n"
--        · (` "×" · ` "m" · ` "n")
--        ])))
--     · ` "m"
--     · ` "n")
--    ])
--   · `suc (`suc `zero))
--   —→⟨ ξ-·₂ V-ƛ (β-ƛ (V-suc (V-suc V-zero))) ⟩
--   (ƛ "n" ⇒
--   case `suc (`suc `zero) [zero⇒ ` "n" |suc "m" ⇒
--   `suc
--   ((μ "+" ⇒
--     (ƛ "m" ⇒
--      (ƛ "n" ⇒
--       case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
--       ])))
--    · ` "m"
--    · ` "n")
--   ])
--   ·
--   case `suc `zero [zero⇒ `zero |suc "m" ⇒
--   (μ "+" ⇒
--   (ƛ "m" ⇒
--    (ƛ "n" ⇒
--     case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
--     ])))
--   · `suc (`suc `zero)
--   ·
--   ((μ "×" ⇒
--    (ƛ "m" ⇒
--     (ƛ "n" ⇒
--      case ` "m" [zero⇒ `zero |suc "m" ⇒
--      (μ "+" ⇒
--       (ƛ "m" ⇒
--        (ƛ "n" ⇒
--         case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
--         ])))
--      · ` "n"
--      · (` "×" · ` "m" · ` "n")
--      ])))
--   · ` "m"
--   · `suc (`suc `zero))
--   ]
--   —→⟨ ξ-·₂ V-ƛ (β-suc V-zero) ⟩
--   (ƛ "n" ⇒
--   case `suc (`suc `zero) [zero⇒ ` "n" |suc "m" ⇒
--   `suc
--   ((μ "+" ⇒
--     (ƛ "m" ⇒
--      (ƛ "n" ⇒
--       case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
--       ])))
--    · ` "m"
--    · ` "n")
--   ])
--   ·
--   ((μ "+" ⇒
--    (ƛ "m" ⇒
--     (ƛ "n" ⇒
--      case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
--      ])))
--   · `suc (`suc `zero)
--   ·
--   ((μ "×" ⇒
--     (ƛ "m" ⇒
--      (ƛ "n" ⇒
--       case ` "m" [zero⇒ `zero |suc "m" ⇒
--       (μ "+" ⇒
--        (ƛ "m" ⇒
--         (ƛ "n" ⇒
--          case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
--          ])))
--       · ` "n"
--       · (` "×" · ` "m" · ` "n")
--       ])))
--    · `zero
--    · `suc (`suc `zero)))
--   —→⟨ ξ-·₂ V-ƛ (ξ-·₁ (ξ-·₁ β-μ)) ⟩
--   (ƛ "n" ⇒
--   case `suc (`suc `zero) [zero⇒ ` "n" |suc "m" ⇒
--   `suc
--   ((μ "+" ⇒
--     (ƛ "m" ⇒
--      (ƛ "n" ⇒
--       case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
--       ])))
--    · ` "m"
--    · ` "n")
--   ])
--   ·
--   ((ƛ "m" ⇒
--    (ƛ "n" ⇒
--     case ` "m" [zero⇒ ` "n" |suc "m" ⇒
--     `suc
--     ((μ "+" ⇒
--       (ƛ "m" ⇒
--        (ƛ "n" ⇒
--         case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
--         ])))
--      · ` "m"
--      · ` "n")
--     ]))
--   · `suc (`suc `zero)
--   ·
--   ((μ "×" ⇒
--     (ƛ "m" ⇒
--      (ƛ "n" ⇒
--       case ` "m" [zero⇒ `zero |suc "m" ⇒
--       (μ "+" ⇒
--        (ƛ "m" ⇒
--         (ƛ "n" ⇒
--          case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
--          ])))
--       · ` "n"
--       · (` "×" · ` "m" · ` "n")
--       ])))
--    · `zero
--    · `suc (`suc `zero)))
--   —→⟨ ξ-·₂ V-ƛ (ξ-·₁ (β-ƛ (V-suc (V-suc V-zero)))) ⟩
--   (ƛ "n" ⇒
--   case `suc (`suc `zero) [zero⇒ ` "n" |suc "m" ⇒
--   `suc
--   ((μ "+" ⇒
--     (ƛ "m" ⇒
--      (ƛ "n" ⇒
--       case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
--       ])))
--    · ` "m"
--    · ` "n")
--   ])
--   ·
--   ((ƛ "n" ⇒
--    case `suc (`suc `zero) [zero⇒ ` "n" |suc "m" ⇒
--    `suc
--    ((μ "+" ⇒
--      (ƛ "m" ⇒
--       (ƛ "n" ⇒
--        case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
--        ])))
--     · ` "m"
--     · ` "n")
--    ])
--   ·
--   ((μ "×" ⇒
--     (ƛ "m" ⇒
--      (ƛ "n" ⇒
--       case ` "m" [zero⇒ `zero |suc "m" ⇒
--       (μ "+" ⇒
--        (ƛ "m" ⇒
--         (ƛ "n" ⇒
--          case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
--          ])))
--       · ` "n"
--       · (` "×" · ` "m" · ` "n")
--       ])))
--    · `zero
--    · `suc (`suc `zero)))
--   —→⟨ ξ-·₂ V-ƛ (ξ-·₂ V-ƛ (ξ-·₁ (ξ-·₁ β-μ))) ⟩
--   (ƛ "n" ⇒
--   case `suc (`suc `zero) [zero⇒ ` "n" |suc "m" ⇒
--   `suc
--   ((μ "+" ⇒
--     (ƛ "m" ⇒
--      (ƛ "n" ⇒
--       case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
--       ])))
--    · ` "m"
--    · ` "n")
--   ])
--   ·
--   ((ƛ "n" ⇒
--    case `suc (`suc `zero) [zero⇒ ` "n" |suc "m" ⇒
--    `suc
--    ((μ "+" ⇒
--      (ƛ "m" ⇒
--       (ƛ "n" ⇒
--        case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
--        ])))
--     · ` "m"
--     · ` "n")
--    ])
--   ·
--   ((ƛ "m" ⇒
--     (ƛ "n" ⇒
--      case ` "m" [zero⇒ `zero |suc "m" ⇒
--      (μ "+" ⇒
--       (ƛ "m" ⇒
--        (ƛ "n" ⇒
--         case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
--         ])))
--      · ` "n"
--      ·
--      ((μ "×" ⇒
--        (ƛ "m" ⇒
--         (ƛ "n" ⇒
--          case ` "m" [zero⇒ `zero |suc "m" ⇒
--          (μ "+" ⇒
--           (ƛ "m" ⇒
--            (ƛ "n" ⇒
--             case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
--             ])))
--          · ` "n"
--          · (` "×" · ` "m" · ` "n")
--          ])))
--       · ` "m"
--       · ` "n")
--      ]))
--    · `zero
--    · `suc (`suc `zero)))
--   —→⟨ ξ-·₂ V-ƛ (ξ-·₂ V-ƛ (ξ-·₁ (β-ƛ V-zero))) ⟩
--   (ƛ "n" ⇒
--   case `suc (`suc `zero) [zero⇒ ` "n" |suc "m" ⇒
--   `suc
--   ((μ "+" ⇒
--     (ƛ "m" ⇒
--      (ƛ "n" ⇒
--       case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
--       ])))
--    · ` "m"
--    · ` "n")
--   ])
--   ·
--   ((ƛ "n" ⇒
--    case `suc (`suc `zero) [zero⇒ ` "n" |suc "m" ⇒
--    `suc
--    ((μ "+" ⇒
--      (ƛ "m" ⇒
--       (ƛ "n" ⇒
--        case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
--        ])))
--     · ` "m"
--     · ` "n")
--    ])
--   ·
--   ((ƛ "n" ⇒
--     case `zero [zero⇒ `zero |suc "m" ⇒
--     (μ "+" ⇒
--      (ƛ "m" ⇒
--       (ƛ "n" ⇒
--        case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
--        ])))
--     · ` "n"
--     ·
--     ((μ "×" ⇒
--       (ƛ "m" ⇒
--        (ƛ "n" ⇒
--         case ` "m" [zero⇒ `zero |suc "m" ⇒
--         (μ "+" ⇒
--          (ƛ "m" ⇒
--           (ƛ "n" ⇒
--            case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
--            ])))
--         · ` "n"
--         · (` "×" · ` "m" · ` "n")
--         ])))
--      · ` "m"
--      · ` "n")
--     ])
--    · `suc (`suc `zero)))
--   —→⟨ ξ-·₂ V-ƛ (ξ-·₂ V-ƛ (β-ƛ (V-suc (V-suc V-zero)))) ⟩
--   (ƛ "n" ⇒
--   case `suc (`suc `zero) [zero⇒ ` "n" |suc "m" ⇒
--   `suc
--   ((μ "+" ⇒
--     (ƛ "m" ⇒
--      (ƛ "n" ⇒
--       case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
--       ])))
--    · ` "m"
--    · ` "n")
--   ])
--   ·
--   ((ƛ "n" ⇒
--    case `suc (`suc `zero) [zero⇒ ` "n" |suc "m" ⇒
--    `suc
--    ((μ "+" ⇒
--      (ƛ "m" ⇒
--       (ƛ "n" ⇒
--        case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
--        ])))
--     · ` "m"
--     · ` "n")
--    ])
--   ·
--   case `zero [zero⇒ `zero |suc "m" ⇒
--   (μ "+" ⇒
--    (ƛ "m" ⇒
--     (ƛ "n" ⇒
--      case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
--      ])))
--   · `suc (`suc `zero)
--   ·
--   ((μ "×" ⇒
--     (ƛ "m" ⇒
--      (ƛ "n" ⇒
--       case ` "m" [zero⇒ `zero |suc "m" ⇒
--       (μ "+" ⇒
--        (ƛ "m" ⇒
--         (ƛ "n" ⇒
--          case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
--          ])))
--       · ` "n"
--       · (` "×" · ` "m" · ` "n")
--       ])))
--    · ` "m"
--    · `suc (`suc `zero))
--   ])
--   —→⟨ ξ-·₂ V-ƛ (ξ-·₂ V-ƛ β-zero) ⟩
--   (ƛ "n" ⇒
--   case `suc (`suc `zero) [zero⇒ ` "n" |suc "m" ⇒
--   `suc
--   ((μ "+" ⇒
--     (ƛ "m" ⇒
--      (ƛ "n" ⇒
--       case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
--       ])))
--    · ` "m"
--    · ` "n")
--   ])
--   ·
--   ((ƛ "n" ⇒
--    case `suc (`suc `zero) [zero⇒ ` "n" |suc "m" ⇒
--    `suc
--    ((μ "+" ⇒
--      (ƛ "m" ⇒
--       (ƛ "n" ⇒
--        case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
--        ])))
--     · ` "m"
--     · ` "n")
--    ])
--   · `zero)
--   —→⟨ ξ-·₂ V-ƛ (β-ƛ V-zero) ⟩
--   (ƛ "n" ⇒
--   case `suc (`suc `zero) [zero⇒ ` "n" |suc "m" ⇒
--   `suc
--   ((μ "+" ⇒
--     (ƛ "m" ⇒
--      (ƛ "n" ⇒
--       case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
--       ])))
--    · ` "m"
--    · ` "n")
--   ])
--   ·
--   case `suc (`suc `zero) [zero⇒ `zero |suc "m" ⇒
--   `suc
--   ((μ "+" ⇒
--    (ƛ "m" ⇒
--     (ƛ "n" ⇒
--      case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
--      ])))
--   · ` "m"
--   · `zero)
--   ]
--   —→⟨ ξ-·₂ V-ƛ (β-suc (V-suc V-zero)) ⟩
--   (ƛ "n" ⇒
--   case `suc (`suc `zero) [zero⇒ ` "n" |suc "m" ⇒
--   `suc
--   ((μ "+" ⇒
--     (ƛ "m" ⇒
--      (ƛ "n" ⇒
--       case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
--       ])))
--    · ` "m"
--    · ` "n")
--   ])
--   ·
--   `suc
--   ((μ "+" ⇒
--    (ƛ "m" ⇒
--     (ƛ "n" ⇒
--      case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
--      ])))
--   · `suc `zero
--   · `zero)
--   —→⟨ ξ-·₂ V-ƛ (ξ-suc (ξ-·₁ (ξ-·₁ β-μ))) ⟩
--   (ƛ "n" ⇒
--   case `suc (`suc `zero) [zero⇒ ` "n" |suc "m" ⇒
--   `suc
--   ((μ "+" ⇒
--     (ƛ "m" ⇒
--      (ƛ "n" ⇒
--       case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
--       ])))
--    · ` "m"
--    · ` "n")
--   ])
--   ·
--   `suc
--   ((ƛ "m" ⇒
--    (ƛ "n" ⇒
--     case ` "m" [zero⇒ ` "n" |suc "m" ⇒
--     `suc
--     ((μ "+" ⇒
--       (ƛ "m" ⇒
--        (ƛ "n" ⇒
--         case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
--         ])))
--      · ` "m"
--      · ` "n")
--     ]))
--   · `suc `zero
--   · `zero)
--   —→⟨ ξ-·₂ V-ƛ (ξ-suc (ξ-·₁ (β-ƛ (V-suc V-zero)))) ⟩
--   (ƛ "n" ⇒
--   case `suc (`suc `zero) [zero⇒ ` "n" |suc "m" ⇒
--   `suc
--   ((μ "+" ⇒
--     (ƛ "m" ⇒
--      (ƛ "n" ⇒
--       case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
--       ])))
--    · ` "m"
--    · ` "n")
--   ])
--   ·
--   `suc
--   ((ƛ "n" ⇒
--    case `suc `zero [zero⇒ ` "n" |suc "m" ⇒
--    `suc
--    ((μ "+" ⇒
--      (ƛ "m" ⇒
--       (ƛ "n" ⇒
--        case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
--        ])))
--     · ` "m"
--     · ` "n")
--    ])
--   · `zero)
--   —→⟨ ξ-·₂ V-ƛ (ξ-suc (β-ƛ V-zero)) ⟩
--   (ƛ "n" ⇒
--   case `suc (`suc `zero) [zero⇒ ` "n" |suc "m" ⇒
--   `suc
--   ((μ "+" ⇒
--     (ƛ "m" ⇒
--      (ƛ "n" ⇒
--       case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
--       ])))
--    · ` "m"
--    · ` "n")
--   ])
--   ·
--   `suc
--   case `suc `zero [zero⇒ `zero |suc "m" ⇒
--   `suc
--   ((μ "+" ⇒
--    (ƛ "m" ⇒
--     (ƛ "n" ⇒
--      case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
--      ])))
--   · ` "m"
--   · `zero)
--   ]
--   —→⟨ ξ-·₂ V-ƛ (ξ-suc (β-suc V-zero)) ⟩
--   (ƛ "n" ⇒
--   case `suc (`suc `zero) [zero⇒ ` "n" |suc "m" ⇒
--   `suc
--   ((μ "+" ⇒
--     (ƛ "m" ⇒
--      (ƛ "n" ⇒
--       case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
--       ])))
--    · ` "m"
--    · ` "n")
--   ])
--   ·
--   `suc
--   (`suc
--   ((μ "+" ⇒
--     (ƛ "m" ⇒
--      (ƛ "n" ⇒
--       case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
--       ])))
--    · `zero
--    · `zero))
--   —→⟨ ξ-·₂ V-ƛ (ξ-suc (ξ-suc (ξ-·₁ (ξ-·₁ β-μ)))) ⟩
--   (ƛ "n" ⇒
--   case `suc (`suc `zero) [zero⇒ ` "n" |suc "m" ⇒
--   `suc
--   ((μ "+" ⇒
--     (ƛ "m" ⇒
--      (ƛ "n" ⇒
--       case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
--       ])))
--    · ` "m"
--    · ` "n")
--   ])
--   ·
--   `suc
--   (`suc
--   ((ƛ "m" ⇒
--     (ƛ "n" ⇒
--      case ` "m" [zero⇒ ` "n" |suc "m" ⇒
--      `suc
--      ((μ "+" ⇒
--        (ƛ "m" ⇒
--         (ƛ "n" ⇒
--          case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
--          ])))
--       · ` "m"
--       · ` "n")
--      ]))
--    · `zero
--    · `zero))
--   —→⟨ ξ-·₂ V-ƛ (ξ-suc (ξ-suc (ξ-·₁ (β-ƛ V-zero)))) ⟩
--   (ƛ "n" ⇒
--   case `suc (`suc `zero) [zero⇒ ` "n" |suc "m" ⇒
--   `suc
--   ((μ "+" ⇒
--     (ƛ "m" ⇒
--      (ƛ "n" ⇒
--       case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
--       ])))
--    · ` "m"
--    · ` "n")
--   ])
--   ·
--   `suc
--   (`suc
--   ((ƛ "n" ⇒
--     case `zero [zero⇒ ` "n" |suc "m" ⇒
--     `suc
--     ((μ "+" ⇒
--       (ƛ "m" ⇒
--        (ƛ "n" ⇒
--         case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
--         ])))
--      · ` "m"
--      · ` "n")
--     ])
--    · `zero))
--   —→⟨ ξ-·₂ V-ƛ (ξ-suc (ξ-suc (β-ƛ V-zero))) ⟩
--   (ƛ "n" ⇒
--   case `suc (`suc `zero) [zero⇒ ` "n" |suc "m" ⇒
--   `suc
--   ((μ "+" ⇒
--     (ƛ "m" ⇒
--      (ƛ "n" ⇒
--       case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
--       ])))
--    · ` "m"
--    · ` "n")
--   ])
--   ·
--   `suc
--   (`suc
--   case `zero [zero⇒ `zero |suc "m" ⇒
--   `suc
--   ((μ "+" ⇒
--     (ƛ "m" ⇒
--      (ƛ "n" ⇒
--       case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
--       ])))
--    · ` "m"
--    · `zero)
--   ])
--   —→⟨ ξ-·₂ V-ƛ (ξ-suc (ξ-suc β-zero)) ⟩
--   (ƛ "n" ⇒
--   case `suc (`suc `zero) [zero⇒ ` "n" |suc "m" ⇒
--   `suc
--   ((μ "+" ⇒
--     (ƛ "m" ⇒
--      (ƛ "n" ⇒
--       case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
--       ])))
--    · ` "m"
--    · ` "n")
--   ])
--   · `suc (`suc `zero)
--   —→⟨ β-ƛ (V-suc (V-suc V-zero)) ⟩
--   case `suc (`suc `zero) [zero⇒ `suc (`suc `zero) |suc "m" ⇒
--   `suc
--   ((μ "+" ⇒
--    (ƛ "m" ⇒
--     (ƛ "n" ⇒
--      case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
--      ])))
--   · ` "m"
--   · `suc (`suc `zero))
--   ]
--   —→⟨ β-suc (V-suc V-zero) ⟩
--   `suc
--   ((μ "+" ⇒
--    (ƛ "m" ⇒
--     (ƛ "n" ⇒
--      case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
--      ])))
--   · `suc `zero
--   · `suc (`suc `zero))
--   —→⟨ ξ-suc (ξ-·₁ (ξ-·₁ β-μ)) ⟩
--   `suc
--   ((ƛ "m" ⇒
--    (ƛ "n" ⇒
--     case ` "m" [zero⇒ ` "n" |suc "m" ⇒
--     `suc
--     ((μ "+" ⇒
--       (ƛ "m" ⇒
--        (ƛ "n" ⇒
--         case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
--         ])))
--      · ` "m"
--      · ` "n")
--     ]))
--   · `suc `zero
--   · `suc (`suc `zero))
--   —→⟨ ξ-suc (ξ-·₁ (β-ƛ (V-suc V-zero))) ⟩
--   `suc
--   ((ƛ "n" ⇒
--    case `suc `zero [zero⇒ ` "n" |suc "m" ⇒
--    `suc
--    ((μ "+" ⇒
--      (ƛ "m" ⇒
--       (ƛ "n" ⇒
--        case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
--        ])))
--     · ` "m"
--     · ` "n")
--    ])
--   · `suc (`suc `zero))
--   —→⟨ ξ-suc (β-ƛ (V-suc (V-suc V-zero))) ⟩
--   `suc
--   case `suc `zero [zero⇒ `suc (`suc `zero) |suc "m" ⇒
--   `suc
--   ((μ "+" ⇒
--    (ƛ "m" ⇒
--     (ƛ "n" ⇒
--      case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
--      ])))
--   · ` "m"
--   · `suc (`suc `zero))
--   ]
--   —→⟨ ξ-suc (β-suc V-zero) ⟩
--   `suc
--   (`suc
--   ((μ "+" ⇒
--     (ƛ "m" ⇒
--      (ƛ "n" ⇒
--       case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
--       ])))
--    · `zero
--    · `suc (`suc `zero)))
--   —→⟨ ξ-suc (ξ-suc (ξ-·₁ (ξ-·₁ β-μ))) ⟩
--   `suc
--   (`suc
--   ((ƛ "m" ⇒
--     (ƛ "n" ⇒
--      case ` "m" [zero⇒ ` "n" |suc "m" ⇒
--      `suc
--      ((μ "+" ⇒
--        (ƛ "m" ⇒
--         (ƛ "n" ⇒
--          case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
--          ])))
--       · ` "m"
--       · ` "n")
--      ]))
--    · `zero
--    · `suc (`suc `zero)))
--   —→⟨ ξ-suc (ξ-suc (ξ-·₁ (β-ƛ V-zero))) ⟩
--   `suc
--   (`suc
--   ((ƛ "n" ⇒
--     case `zero [zero⇒ ` "n" |suc "m" ⇒
--     `suc
--     ((μ "+" ⇒
--       (ƛ "m" ⇒
--        (ƛ "n" ⇒
--         case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
--         ])))
--      · ` "m"
--      · ` "n")
--     ])
--    · `suc (`suc `zero)))
--   —→⟨ ξ-suc (ξ-suc (β-ƛ (V-suc (V-suc V-zero)))) ⟩
--   `suc
--   (`suc
--   case `zero [zero⇒ `suc (`suc `zero) |suc "m" ⇒
--   `suc
--   ((μ "+" ⇒
--     (ƛ "m" ⇒
--      (ƛ "n" ⇒
--       case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
--       ])))
--    · ` "m"
--    · `suc (`suc `zero))
--   ])
--   —→⟨ ξ-suc (ξ-suc β-zero) ⟩ `suc (`suc (`suc (`suc `zero))) ∎)
--   (done (V-suc (V-suc (V-suc (V-suc V-zero)))))
-- mul-eval = refl
