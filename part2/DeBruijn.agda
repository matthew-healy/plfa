module plfa.part2.DeBruijn where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (ℕ; zero; suc)
open import Relation.Nullary using (¬_)

-- Syntax

infix  4 _⊢_
infix  4 _∋_
infixl 5 _,_

infixr 7 _⇒_

infix  5 ƛ_
infix  5 μ_
infixl 7 _·_
infix  8 `suc_
infix  9 `_
infix  9 S_
infix  9 #_

-- Types

data Type : Set where
  _⇒_ : Type → Type → Type
  `ℕ  : Type

-- Contexts

data Context : Set where
  ∅   : Context
  _,_ : Context → Type → Context

_ : Context
_ = ∅ , `ℕ ⇒ `ℕ , `ℕ

-- Variables and the lookup judgement

data _∋_ : Context → Type → Set where
  Z : ∀ {Γ A}
      ---------
    → Γ , A ∋ A

  S_ : ∀ {Γ A B}
    → Γ ∋ A
      ---------
    → Γ , B ∋ A

-- Previously: ∅ , "s" ⦂ `ℕ ⇒ `ℕ , "z" ⦂ `ℕ ∋ "z" ⦂ `ℕ
_ : ∅ , `ℕ ⇒ `ℕ , `ℕ ∋ `ℕ
_ = Z

-- Previously: ∅ , "s" ⦂ `ℕ ⇒ `ℕ , "z" ⦂ `ℕ ∋ "s" ⦂ `ℕ ⇒ `ℕ
_ : ∅ , `ℕ ⇒ `ℕ , `ℕ ∋ `ℕ ⇒ `ℕ
_ = S Z

-- Terms and the typing judgement

data _⊢_ : Context → Type → Set where
  `_ : ∀ {Γ A}
    → Γ ∋ A
      -----
    → Γ ⊢ A

  ƛ_ : ∀ {Γ A B}
    → Γ , A ⊢ B
      ---------
    → Γ ⊢ A ⇒ B

  _·_ : ∀ {Γ A B}
    → Γ ⊢ A ⇒ B
    → Γ ⊢ A
      ---------
    → Γ ⊢ B

  `zero : ∀ {Γ}
      -------
    → Γ ⊢ `ℕ

  `suc_ : ∀ {Γ}
    → Γ ⊢ `ℕ
      -------
    → Γ ⊢ `ℕ

  case : ∀ {Γ A}
    → Γ ⊢ `ℕ
    → Γ ⊢ A
    → Γ , `ℕ ⊢ A
      ----------
    → Γ ⊢ A

  μ_ : ∀ {Γ A}
    → Γ , A ⊢ A
      ---------
    → Γ ⊢ A

-- Previously: ∅ , "s" ⦂ `ℕ ⇒ `ℕ , "z" ⦂ `ℕ ⊢ ` "z" ⦂ `ℕ
_ : ∅ , `ℕ ⇒ `ℕ , `ℕ ⊢ `ℕ
_ = ` Z

-- Previously: ∅ , "s" ⦂ `ℕ ⇒ `ℕ , "z" ⦂ `ℕ ⊢ ` "s" ⦂ `ℕ ⇒ `ℕ
_ : ∅ , `ℕ ⇒ `ℕ , `ℕ ⊢ `ℕ ⇒ `ℕ
_ = ` S Z

-- Previously: ∅ , "s" ⦂ `ℕ ⇒ `ℕ , "z" ⦂ `ℕ ⊢ ` "s" · ` "z" ⦂  `ℕ
_ : ∅ , `ℕ ⇒ `ℕ , `ℕ ⊢ `ℕ
_ = ` S Z · ` Z

-- Previously: ∅ , "s" ⦂ `ℕ ⇒ `ℕ , "z" ⦂ `ℕ ⊢ ` "s" · (` "s" · ` "z") ⦂  `ℕ
_ : ∅ , `ℕ ⇒ `ℕ , `ℕ ⊢ `ℕ
_ = ` S Z · (` S Z · ` Z)

-- Previously: ∅ , "s" ⦂ `ℕ ⇒ `ℕ ⊢ (ƛ "z" ⇒ ` "s" · (` "s" · ` "z")) ⦂  `ℕ ⇒ `ℕ
_ : ∅ , `ℕ ⇒ `ℕ ⊢ `ℕ ⇒ `ℕ
_ = ƛ (` S Z · (` S Z · ` Z ))

-- Previously: ∅ ⊢ ƛ "s" ⇒ ƛ "z" ⇒ ` "s" · (` "s" · ` "z")) ⦂  (`ℕ ⇒ `ℕ) ⇒ `ℕ ⇒ `ℕ
_ : ∅ ⊢ (`ℕ ⇒ `ℕ) ⇒ `ℕ ⇒ `ℕ
_ = ƛ (ƛ ` S Z · (` S Z · ` Z))

-- Abbreviating de Bruijn indices

lookup : Context → ℕ → Type
lookup (Γ , A) zero    = A
lookup (Γ , _) (suc n) = lookup Γ n
lookup ∅       _       = ⊥-elim impossible
  where postulate impossible : ⊥

count : ∀ {Γ} → (n : ℕ) → Γ ∋ lookup Γ n
count {Γ , _} zero    = Z
count {Γ , _} (suc n) = S (count n)
count {∅}     _       = ⊥-elim impossible
  where postulate impossible : ⊥

#_ : ∀ {Γ} → (n : ℕ) → Γ ⊢ lookup Γ n
# n = ` count n

-- Can rewrite above examples more compactly, e.g.:
_ : ∅ ⊢ (`ℕ ⇒ `ℕ) ⇒ `ℕ ⇒ `ℕ
_ = ƛ ƛ (# 1 · (# 1 · # 0))

-- Test examples

-- Two plus two on naturals
two : ∀ {Γ} → Γ ⊢ `ℕ
two = `suc `suc `zero

plus : ∀ {Γ} → Γ ⊢ `ℕ ⇒ `ℕ ⇒ `ℕ
plus = μ ƛ ƛ (case (# 1) (# 0) (`suc (# 3 · # 0 · # 1)))

2+2 : ∀ {Γ} → Γ ⊢ `ℕ
2+2 = plus · two · two

-- Two plus two on church numerals
Ch : Type → Type
Ch A = (A ⇒ A) ⇒ A ⇒ A

twoᶜ : ∀ {Γ A} → Γ ⊢ Ch A
twoᶜ = ƛ ƛ (# 1 · (# 1 · # 0))

plusᶜ : ∀ {Γ A} → Γ ⊢ Ch A ⇒ Ch A ⇒ Ch A
plusᶜ = ƛ ƛ ƛ ƛ (# 3 · # 1 · (# 2 · # 1 · # 0))

sucᶜ : ∀ {Γ} → Γ ⊢ `ℕ ⇒ `ℕ
sucᶜ = ƛ `suc (# 0)

2+2ᶜ : ∀ {Γ} → Γ ⊢ `ℕ
2+2ᶜ = plusᶜ · twoᶜ · twoᶜ · sucᶜ · `zero


-- Exercise: mul
mul : ∀ {Γ} → Γ ⊢ `ℕ ⇒ `ℕ ⇒ `ℕ
mul = μ ƛ ƛ (case (# 1) `zero (plus · # 1 · (# 3 · # 0 · # 1)))

-- Renaming

ext : ∀ {Γ Δ}
  → (∀ {A} →       Γ ∋ A →     Δ ∋ A)
    ---------------------------------
  → (∀ {A B} → Γ , B ∋ A → Δ , B ∋ A)
ext ρ Z     = Z
ext ρ (S x) = S (ρ x)

rename : ∀ {Γ Δ}
  → (∀ {A} → Γ ∋ A → Δ ∋ A)
    -----------------------
  → (∀ {A} → Γ ⊢ A → Δ ⊢ A)
rename ρ (` x)        = ` (ρ x)
rename ρ (ƛ N)        = ƛ (rename (ext ρ) N)
rename ρ (L · M)      = (rename ρ L) · (rename ρ M)
rename ρ `zero        = `zero
rename ρ (`suc M)     = `suc (rename ρ M)
rename ρ (case L M N) = case (rename ρ L) (rename ρ M) (rename (ext ρ) N)
rename ρ (μ N)        = μ (rename (ext ρ) N)

-- Example
M₀ : ∅ , `ℕ ⇒ `ℕ ⊢ `ℕ ⇒ `ℕ
M₀ = ƛ (# 1 · (# 1 · # 0))

M₁ : ∅ , `ℕ ⇒ `ℕ , `ℕ ⊢ `ℕ ⇒ `ℕ
M₁ = ƛ (# 2 · (# 2 · # 0))

_ : rename S_ M₀ ≡ M₁
_ = refl

-- Simultanous Substitution

exts : ∀ {Γ Δ}
  → (∀ {A} →       Γ ∋ A →     Δ ⊢ A)
    ---------------------------------
  → (∀ {A B} → Γ , B ∋ A → Δ , B ⊢ A)
exts σ Z     = ` Z
exts σ (S x) = rename S_ (σ x)

subst : ∀ {Γ Δ}
  → (∀ {A} → Γ ∋ A → Δ ⊢ A)
    -----------------------
  → (∀ {A} → Γ ⊢ A → Δ ⊢ A)
subst σ (` k)        = σ k
subst σ (ƛ N)        = ƛ (subst (exts σ) N)
subst σ (L · M)      = (subst σ L) · (subst σ M)
subst σ `zero        = `zero
subst σ (`suc M)     = `suc subst σ M
subst σ (case L M N) = case (subst σ L) (subst σ M) (subst (exts σ) N)
subst σ (μ N)        = μ (subst (exts σ) N)

-- Single substitution

_[_] : ∀ {Γ A B}
  → Γ , B ⊢ A
  → Γ ⊢ B
    ---------
  → Γ ⊢ A
_[_] {Γ} {A} {B} N M = subst {Γ , B} {Γ} σ {A} N
  where
  σ : ∀ {A} → Γ , B ∋ A → Γ ⊢ A
  σ Z     = M
  σ (S x) = ` x

-- Example
M₂ : ∅ , `ℕ ⇒ `ℕ ⊢ `ℕ ⇒ `ℕ
M₂ = ƛ # 1 · (# 1 · # 0)

M₃ : ∅ ⊢ `ℕ ⇒ `ℕ
M₃ = ƛ `suc # 0

M₄ : ∅ ⊢ `ℕ ⇒ `ℕ
M₄ = ƛ (ƛ `suc # 0) · ((ƛ `suc # 0) · # 0)

_ : M₂ [ M₃ ] ≡ M₄
_ = refl

-- Example
-- (ƛ "x" ⇒ ` "x" · ` "y") [ "y" := ` "x" · `zero ]
-- Should yield ƛ "z" ⇒ ` "z" · (` "x" · `zero)
-- Was difficult without de Bruijn indices as we needed to rename the bound
-- variable.
M₅ : ∅ , `ℕ ⇒ `ℕ , `ℕ ⊢ (`ℕ ⇒ `ℕ) ⇒ `ℕ
M₅ = ƛ # 0 · # 1

M₆ : ∅ , `ℕ ⇒ `ℕ ⊢ `ℕ
M₆ = # 0 · `zero

M₇ : ∅ , `ℕ ⇒ `ℕ ⊢ (`ℕ ⇒ `ℕ) ⇒ `ℕ
M₇ = ƛ (# 0 · (# 1 · `zero))

_ : M₅ [ M₆ ] ≡ M₇
_ = refl

-- Values

data Value : ∀ {Γ A} → Γ ⊢ A → Set where
  V-ƛ : ∀ {Γ A B} {N : Γ , A ⊢ B}
      ---------------------------
    → Value (ƛ N)

  V-zero : ∀ {Γ}
      -----------------
    → Value (`zero {Γ})

  V-suc : ∀ {Γ} {V : Γ ⊢ `ℕ}
    → Value V
      --------------
    → Value (`suc V)

-- Reduction

infix 2 _—→_

data _—→_ : ∀ {Γ A} → (Γ ⊢ A) → (Γ ⊢ A) → Set where
  ξ-·₁ : ∀ {Γ A B} {L L′ : Γ ⊢ A ⇒ B} {M : Γ ⊢ A}
    → L —→ L′
      ---------------
    → L · M —→ L′ · M

  ξ-·₂ : ∀ {Γ A B} {V : Γ ⊢ A ⇒ B} {M M′ : Γ ⊢ A}
    → Value V
    → M —→ M′
      ---------------
    → V · M —→ V · M′

  β-ƛ : ∀ {Γ A B} {N : Γ , A ⊢ B} {W : Γ ⊢ A}
    → Value W
      --------------------
    → (ƛ N) · W —→ N [ W ]

  ξ-suc : ∀ {Γ} {M M′ : Γ ⊢ `ℕ}
    → M —→ M′
      -----------------
    → `suc M —→ `suc M′

  ξ-case : ∀ {Γ A} {L L′ : Γ ⊢ `ℕ} {M : Γ ⊢ A} {N : Γ , `ℕ ⊢ A}
    → L —→ L′
      -------------------------
    → case L M N —→ case L′ M N

  β-zero : ∀ {Γ A} {M : Γ ⊢ A} {N : Γ , `ℕ ⊢ A}
      -------------------
    → case `zero M N —→ M

  β-suc : ∀ {Γ A} {V : Γ ⊢ `ℕ} {M : Γ ⊢ A} {N : Γ , `ℕ ⊢ A}
    → Value V
      ----------------------------
    → case (`suc V) M N —→ N [ V ]

  β-μ : ∀ {Γ A} {N : Γ , A ⊢ A}
      ----------------
    → μ N —→ N [ μ N ]

-- Reflexive and transitive closure
infix  2 _—↠_
infix  1 begin_
infixr 2 _—→⟨_⟩_
infix  3 _∎

data _—↠_ : ∀ {Γ A} → (Γ ⊢ A) → (Γ ⊢ A) → Set where
  _∎ : ∀ {Γ A} (M : Γ ⊢ A)
      ------
    → M —↠ M

  _—→⟨_⟩_ : ∀ {Γ A} (L : Γ ⊢ A) {M N : Γ ⊢ A}
    → L —→ M
    → M —↠ N
      ------
    → L —↠ N

begin_ : ∀ {Γ A} {M N : Γ ⊢ A}
  → M —↠ N
    ------
  → M —↠ N
begin M—↠N = M—↠N

-- Examples
_ : twoᶜ · sucᶜ · `zero {∅} —↠ `suc `suc `zero
_ = begin
      twoᶜ · sucᶜ · `zero
    —→⟨ ξ-·₁ (β-ƛ V-ƛ) ⟩
      (ƛ (sucᶜ · (sucᶜ · # 0))) · `zero
    —→⟨ β-ƛ V-zero ⟩
      sucᶜ · (sucᶜ · `zero)
    —→⟨ ξ-·₂ V-ƛ (β-ƛ V-zero) ⟩
      sucᶜ · `suc `zero
    —→⟨ β-ƛ (V-suc V-zero) ⟩
      `suc (`suc `zero)
    ∎

_ : plus {∅} · two · two —↠ `suc `suc `suc `suc `zero
_ =
    plus · two · two
  —→⟨ ξ-·₁ (ξ-·₁ β-μ) ⟩
    (ƛ ƛ case (` S Z) (` Z) (`suc (plus · ` Z · ` S Z))) · two · two
  —→⟨ ξ-·₁ (β-ƛ (V-suc (V-suc V-zero))) ⟩
    (ƛ case two (` Z) (`suc (plus · ` Z · ` S Z))) · two
  —→⟨ β-ƛ (V-suc (V-suc V-zero)) ⟩
    case two two (`suc (plus · ` Z · two))
  —→⟨ β-suc (V-suc V-zero) ⟩
    `suc (plus · `suc `zero · two)
  —→⟨ ξ-suc (ξ-·₁ (ξ-·₁ β-μ)) ⟩
    `suc ((ƛ ƛ case (` S Z) (` Z) (`suc (plus · ` Z · ` S Z)))
      · `suc `zero · two)
  —→⟨ ξ-suc (ξ-·₁ (β-ƛ (V-suc V-zero))) ⟩
    `suc ((ƛ case (`suc `zero) (` Z) (`suc (plus · ` Z · ` S Z))) · two)
  —→⟨ ξ-suc (β-ƛ (V-suc (V-suc V-zero))) ⟩
    `suc (case (`suc `zero) (two) (`suc (plus · ` Z · two)))
  —→⟨ ξ-suc (β-suc V-zero) ⟩
    `suc (`suc (plus · `zero · two))
  —→⟨ ξ-suc (ξ-suc (ξ-·₁ (ξ-·₁ β-μ))) ⟩
    `suc (`suc ((ƛ ƛ case (` S Z) (` Z) (`suc (plus · ` Z · ` S Z)))
      · `zero · two))
  —→⟨ ξ-suc (ξ-suc (ξ-·₁ (β-ƛ V-zero))) ⟩
    `suc (`suc ((ƛ case `zero (` Z) (`suc (plus · ` Z · ` S Z))) · two))
  —→⟨ ξ-suc (ξ-suc (β-ƛ (V-suc (V-suc V-zero)))) ⟩
    `suc (`suc (case `zero (two) (`suc (plus · ` Z · two))))
  —→⟨ ξ-suc (ξ-suc β-zero) ⟩
   `suc (`suc (`suc (`suc `zero)))
  ∎

_ : plusᶜ · twoᶜ · twoᶜ · sucᶜ · `zero —↠ `suc `suc `suc `suc `zero {∅}
_ =
  begin
    plusᶜ · twoᶜ · twoᶜ · sucᶜ · `zero
  —→⟨ ξ-·₁ (ξ-·₁ (ξ-·₁ (β-ƛ V-ƛ))) ⟩
    (ƛ ƛ ƛ twoᶜ · ` S Z · (` S S Z · ` S Z · ` Z)) · twoᶜ · sucᶜ · `zero
  —→⟨ ξ-·₁ (ξ-·₁ (β-ƛ V-ƛ)) ⟩
    (ƛ ƛ twoᶜ · ` S Z · (twoᶜ · ` S Z · ` Z)) · sucᶜ · `zero
  —→⟨ ξ-·₁ (β-ƛ V-ƛ) ⟩
    (ƛ twoᶜ · sucᶜ · (twoᶜ · sucᶜ · ` Z)) · `zero
  —→⟨ β-ƛ V-zero ⟩
    twoᶜ · sucᶜ · (twoᶜ · sucᶜ · `zero)
  —→⟨ ξ-·₁ (β-ƛ V-ƛ) ⟩
    (ƛ sucᶜ · (sucᶜ · ` Z)) · (twoᶜ · sucᶜ · `zero)
  —→⟨ ξ-·₂ V-ƛ (ξ-·₁ (β-ƛ V-ƛ)) ⟩
    (ƛ sucᶜ · (sucᶜ · ` Z)) · ((ƛ sucᶜ · (sucᶜ · ` Z)) · `zero)
  —→⟨ ξ-·₂ V-ƛ (β-ƛ V-zero) ⟩
    (ƛ sucᶜ · (sucᶜ · ` Z)) · (sucᶜ · (sucᶜ · `zero))
  —→⟨ ξ-·₂ V-ƛ (ξ-·₂ V-ƛ (β-ƛ V-zero)) ⟩
    (ƛ sucᶜ · (sucᶜ · ` Z)) · (sucᶜ · `suc `zero)
  —→⟨ ξ-·₂ V-ƛ (β-ƛ (V-suc V-zero)) ⟩
    (ƛ sucᶜ · (sucᶜ · ` Z)) · `suc (`suc `zero)
  —→⟨ β-ƛ (V-suc (V-suc V-zero)) ⟩
    sucᶜ · (sucᶜ · `suc (`suc `zero))
  —→⟨ ξ-·₂ V-ƛ (β-ƛ (V-suc (V-suc V-zero))) ⟩
    sucᶜ · `suc (`suc (`suc `zero))
  —→⟨ β-ƛ (V-suc (V-suc (V-suc V-zero))) ⟩
    `suc (`suc (`suc (`suc `zero)))
  ∎

-- Values do not reduce

-- Exercise: V¬—→

V¬—→ : ∀ {Γ A M N}
  → Value {Γ} {A} M
    ---------------
  → ¬ (M —→ N)
V¬—→ (V-suc VM) (ξ-suc M—→N) = V¬—→ VM M—→N

—→¬V : ∀ {Γ A M N}
  → _—→_ {Γ} {A} M N
    ----------------
  → ¬ Value M
—→¬V M—→N VM = V¬—→ VM M—→N

-- Progress
data Progress {A} (M : ∅ ⊢ A) : Set where
  step : ∀ {N : ∅ ⊢ A}
    → M —→ N
      ----------
    → Progress M

  done :
      Value M
      ----------
    → Progress M

progress : ∀ {A} → (M : ∅ ⊢ A) → Progress M
progress (ƛ N)                   = done V-ƛ
progress (L · M) with progress L
... | step L—→L′                      = step (ξ-·₁ L—→L′)
... | done V-ƛ with progress M
...   | step M—→M′                    = step (ξ-·₂ V-ƛ M—→M′)
...   | done VM                       = step (β-ƛ VM)
progress `zero                        = done V-zero
progress (`suc N) with progress N
... | step N—→N′                      = step (ξ-suc N—→N′)
... | done VN                         = done (V-suc VN)
progress (case L M N) with progress L
... | step L—→L′                      = step (ξ-case L—→L′)
... | done V-zero                     = step β-zero
... | done (V-suc VL)                 = step (β-suc VL)
progress (μ N)                        = step β-μ

-- Evaluation

record Gas : Set where
  constructor gas
  field
    amount : ℕ

data Finished {Γ A} (N : Γ ⊢ A) : Set where
  done :
      Value N
      ----------
    → Finished N

  out-of-gas :
      ----------
      Finished N

data Steps : ∀ {A} → ∅ ⊢ A → Set where
  steps : ∀ {A} {L N : ∅ ⊢ A}
    → L —↠ N
    → Finished N
      -----------
    → Steps L

eval : ∀ {A}
  → Gas
  → (L : ∅ ⊢ A)
    -----------
  → Steps L
eval (gas zero) L                       = steps (L ∎) out-of-gas
eval (gas (suc m)) L with progress L
... | done VL                           = steps (L ∎) (done VL)
... | step {M} L—→M with eval (gas m) M
...   | steps M—↠N fin                  = steps (L —→⟨ L—→M ⟩ M—↠N) fin

-- Examples

-- This loops forever, so runs out of gas
sucμ : ∅ ⊢ `ℕ
sucμ = μ (`suc (# 0))

_ : eval (gas 3) sucμ ≡
  steps
   (μ `suc ` Z
   —→⟨ β-μ ⟩
    `suc (μ `suc ` Z)
   —→⟨ ξ-suc β-μ ⟩
    `suc (`suc (μ `suc ` Z))
   —→⟨ ξ-suc (ξ-suc β-μ) ⟩
    `suc (`suc (`suc (μ `suc ` Z)))
   ∎)
   out-of-gas
_ = refl

-- The Church numeral two
_ : eval (gas 100) (twoᶜ · sucᶜ · `zero) ≡
  steps
   ((ƛ (ƛ ` (S Z) · (` (S Z) · ` Z))) · (ƛ `suc ` Z) · `zero
   —→⟨ ξ-·₁ (β-ƛ V-ƛ) ⟩
    (ƛ (ƛ `suc ` Z) · ((ƛ `suc ` Z) · ` Z)) · `zero
   —→⟨ β-ƛ V-zero ⟩
    (ƛ `suc ` Z) · ((ƛ `suc ` Z) · `zero)
   —→⟨ ξ-·₂ V-ƛ (β-ƛ V-zero) ⟩
    (ƛ `suc ` Z) · `suc `zero
   —→⟨ β-ƛ (V-suc V-zero) ⟩
    `suc (`suc `zero)
   ∎)
   (done (V-suc (V-suc V-zero)))
_ = refl

-- Exercise: mul-example

-- Leaving this commented out as, unsurprisingly, Agda does not seem to enjoy
-- typechecking this 600+ line type signature.

-- mul-example : eval (gas 100) (mul · two · two) ≡
--   steps
--   ((μ
--   (ƛ
--    (ƛ
--     case (` (S Z)) `zero
--     ((μ
--       (ƛ
--        (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
--      · ` (S Z)
--      · (` (S (S (S Z))) · ` Z · ` (S Z))))))
--   · `suc (`suc `zero)
--   · `suc (`suc `zero)
--   —→⟨ ξ-·₁ (ξ-·₁ β-μ) ⟩
--   (ƛ
--   (ƛ
--    case (` (S Z)) `zero
--    ((μ
--      (ƛ
--       (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
--     · ` (S Z)
--     ·
--     ((μ
--       (ƛ
--        (ƛ
--         case (` (S Z)) `zero
--         ((μ
--           (ƛ
--            (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
--          · ` (S Z)
--          · (` (S (S (S Z))) · ` Z · ` (S Z))))))
--      · ` Z
--      · ` (S Z)))))
--   · `suc (`suc `zero)
--   · `suc (`suc `zero)
--   —→⟨ ξ-·₁ (β-ƛ (V-suc (V-suc V-zero))) ⟩
--   (ƛ
--   case (`suc (`suc `zero)) `zero
--   ((μ
--     (ƛ
--      (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
--    · ` (S Z)
--    ·
--    ((μ
--      (ƛ
--       (ƛ
--        case (` (S Z)) `zero
--        ((μ
--          (ƛ
--           (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
--         · ` (S Z)
--         · (` (S (S (S Z))) · ` Z · ` (S Z))))))
--     · ` Z
--     · ` (S Z))))
--   · `suc (`suc `zero)
--   —→⟨ β-ƛ (V-suc (V-suc V-zero)) ⟩
--   case (`suc (`suc `zero)) `zero
--   ((μ
--    (ƛ
--     (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
--   · `suc (`suc `zero)
--   ·
--   ((μ
--     (ƛ
--      (ƛ
--       case (` (S Z)) `zero
--       ((μ
--         (ƛ
--          (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
--        · ` (S Z)
--        · (` (S (S (S Z))) · ` Z · ` (S Z))))))
--    · ` Z
--    · `suc (`suc `zero)))
--   —→⟨ β-suc (V-suc V-zero) ⟩
--   (μ
--   (ƛ
--    (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
--   · `suc (`suc `zero)
--   ·
--   ((μ
--    (ƛ
--     (ƛ
--      case (` (S Z)) `zero
--      ((μ
--        (ƛ
--         (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
--       · ` (S Z)
--       · (` (S (S (S Z))) · ` Z · ` (S Z))))))
--   · `suc `zero
--   · `suc (`suc `zero))
--   —→⟨ ξ-·₁ (ξ-·₁ β-μ) ⟩
--   (ƛ
--   (ƛ
--    case (` (S Z)) (` Z)
--    (`suc
--     ((μ
--       (ƛ
--        (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
--      · ` Z
--      · ` (S Z)))))
--   · `suc (`suc `zero)
--   ·
--   ((μ
--    (ƛ
--     (ƛ
--      case (` (S Z)) `zero
--      ((μ
--        (ƛ
--         (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
--       · ` (S Z)
--       · (` (S (S (S Z))) · ` Z · ` (S Z))))))
--   · `suc `zero
--   · `suc (`suc `zero))
--   —→⟨ ξ-·₁ (β-ƛ (V-suc (V-suc V-zero))) ⟩
--   (ƛ
--   case (`suc (`suc `zero)) (` Z)
--   (`suc
--    ((μ
--      (ƛ
--       (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
--     · ` Z
--     · ` (S Z))))
--   ·
--   ((μ
--    (ƛ
--     (ƛ
--      case (` (S Z)) `zero
--      ((μ
--        (ƛ
--         (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
--       · ` (S Z)
--       · (` (S (S (S Z))) · ` Z · ` (S Z))))))
--   · `suc `zero
--   · `suc (`suc `zero))
--   —→⟨ ξ-·₂ V-ƛ (ξ-·₁ (ξ-·₁ β-μ)) ⟩
--   (ƛ
--   case (`suc (`suc `zero)) (` Z)
--   (`suc
--    ((μ
--      (ƛ
--       (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
--     · ` Z
--     · ` (S Z))))
--   ·
--   ((ƛ
--    (ƛ
--     case (` (S Z)) `zero
--     ((μ
--       (ƛ
--        (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
--      · ` (S Z)
--      ·
--      ((μ
--        (ƛ
--         (ƛ
--          case (` (S Z)) `zero
--          ((μ
--            (ƛ
--             (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
--           · ` (S Z)
--           · (` (S (S (S Z))) · ` Z · ` (S Z))))))
--       · ` Z
--       · ` (S Z)))))
--   · `suc `zero
--   · `suc (`suc `zero))
--   —→⟨ ξ-·₂ V-ƛ (ξ-·₁ (β-ƛ (V-suc V-zero))) ⟩
--   (ƛ
--   case (`suc (`suc `zero)) (` Z)
--   (`suc
--    ((μ
--      (ƛ
--       (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
--     · ` Z
--     · ` (S Z))))
--   ·
--   ((ƛ
--    case (`suc `zero) `zero
--    ((μ
--      (ƛ
--       (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
--     · ` (S Z)
--     ·
--     ((μ
--       (ƛ
--        (ƛ
--         case (` (S Z)) `zero
--         ((μ
--           (ƛ
--            (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
--          · ` (S Z)
--          · (` (S (S (S Z))) · ` Z · ` (S Z))))))
--      · ` Z
--      · ` (S Z))))
--   · `suc (`suc `zero))
--   —→⟨ ξ-·₂ V-ƛ (β-ƛ (V-suc (V-suc V-zero))) ⟩
--   (ƛ
--   case (`suc (`suc `zero)) (` Z)
--   (`suc
--    ((μ
--      (ƛ
--       (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
--     · ` Z
--     · ` (S Z))))
--   ·
--   case (`suc `zero) `zero
--   ((μ
--    (ƛ
--     (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
--   · `suc (`suc `zero)
--   ·
--   ((μ
--     (ƛ
--      (ƛ
--       case (` (S Z)) `zero
--       ((μ
--         (ƛ
--          (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
--        · ` (S Z)
--        · (` (S (S (S Z))) · ` Z · ` (S Z))))))
--    · ` Z
--    · `suc (`suc `zero)))
--   —→⟨ ξ-·₂ V-ƛ (β-suc V-zero) ⟩
--   (ƛ
--   case (`suc (`suc `zero)) (` Z)
--   (`suc
--    ((μ
--      (ƛ
--       (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
--     · ` Z
--     · ` (S Z))))
--   ·
--   ((μ
--    (ƛ
--     (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
--   · `suc (`suc `zero)
--   ·
--   ((μ
--     (ƛ
--      (ƛ
--       case (` (S Z)) `zero
--       ((μ
--         (ƛ
--          (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
--        · ` (S Z)
--        · (` (S (S (S Z))) · ` Z · ` (S Z))))))
--    · `zero
--    · `suc (`suc `zero)))
--   —→⟨ ξ-·₂ V-ƛ (ξ-·₁ (ξ-·₁ β-μ)) ⟩
--   (ƛ
--   case (`suc (`suc `zero)) (` Z)
--   (`suc
--    ((μ
--      (ƛ
--       (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
--     · ` Z
--     · ` (S Z))))
--   ·
--   ((ƛ
--    (ƛ
--     case (` (S Z)) (` Z)
--     (`suc
--      ((μ
--        (ƛ
--         (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
--       · ` Z
--       · ` (S Z)))))
--   · `suc (`suc `zero)
--   ·
--   ((μ
--     (ƛ
--      (ƛ
--       case (` (S Z)) `zero
--       ((μ
--         (ƛ
--          (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
--        · ` (S Z)
--        · (` (S (S (S Z))) · ` Z · ` (S Z))))))
--    · `zero
--    · `suc (`suc `zero)))
--   —→⟨ ξ-·₂ V-ƛ (ξ-·₁ (β-ƛ (V-suc (V-suc V-zero)))) ⟩
--   (ƛ
--   case (`suc (`suc `zero)) (` Z)
--   (`suc
--    ((μ
--      (ƛ
--       (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
--     · ` Z
--     · ` (S Z))))
--   ·
--   ((ƛ
--    case (`suc (`suc `zero)) (` Z)
--    (`suc
--     ((μ
--       (ƛ
--        (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
--      · ` Z
--      · ` (S Z))))
--   ·
--   ((μ
--     (ƛ
--      (ƛ
--       case (` (S Z)) `zero
--       ((μ
--         (ƛ
--          (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
--        · ` (S Z)
--        · (` (S (S (S Z))) · ` Z · ` (S Z))))))
--    · `zero
--    · `suc (`suc `zero)))
--   —→⟨ ξ-·₂ V-ƛ (ξ-·₂ V-ƛ (ξ-·₁ (ξ-·₁ β-μ))) ⟩
--   (ƛ
--   case (`suc (`suc `zero)) (` Z)
--   (`suc
--    ((μ
--      (ƛ
--       (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
--     · ` Z
--     · ` (S Z))))
--   ·
--   ((ƛ
--    case (`suc (`suc `zero)) (` Z)
--    (`suc
--     ((μ
--       (ƛ
--        (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
--      · ` Z
--      · ` (S Z))))
--   ·
--   ((ƛ
--     (ƛ
--      case (` (S Z)) `zero
--      ((μ
--        (ƛ
--         (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
--       · ` (S Z)
--       ·
--       ((μ
--         (ƛ
--          (ƛ
--           case (` (S Z)) `zero
--           ((μ
--             (ƛ
--              (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
--            · ` (S Z)
--            · (` (S (S (S Z))) · ` Z · ` (S Z))))))
--        · ` Z
--        · ` (S Z)))))
--    · `zero
--    · `suc (`suc `zero)))
--   —→⟨ ξ-·₂ V-ƛ (ξ-·₂ V-ƛ (ξ-·₁ (β-ƛ V-zero))) ⟩
--   (ƛ
--   case (`suc (`suc `zero)) (` Z)
--   (`suc
--    ((μ
--      (ƛ
--       (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
--     · ` Z
--     · ` (S Z))))
--   ·
--   ((ƛ
--    case (`suc (`suc `zero)) (` Z)
--    (`suc
--     ((μ
--       (ƛ
--        (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
--      · ` Z
--      · ` (S Z))))
--   ·
--   ((ƛ
--     case `zero `zero
--     ((μ
--       (ƛ
--        (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
--      · ` (S Z)
--      ·
--      ((μ
--        (ƛ
--         (ƛ
--          case (` (S Z)) `zero
--          ((μ
--            (ƛ
--             (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
--           · ` (S Z)
--           · (` (S (S (S Z))) · ` Z · ` (S Z))))))
--       · ` Z
--       · ` (S Z))))
--    · `suc (`suc `zero)))
--   —→⟨ ξ-·₂ V-ƛ (ξ-·₂ V-ƛ (β-ƛ (V-suc (V-suc V-zero)))) ⟩
--   (ƛ
--   case (`suc (`suc `zero)) (` Z)
--   (`suc
--    ((μ
--      (ƛ
--       (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
--     · ` Z
--     · ` (S Z))))
--   ·
--   ((ƛ
--    case (`suc (`suc `zero)) (` Z)
--    (`suc
--     ((μ
--       (ƛ
--        (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
--      · ` Z
--      · ` (S Z))))
--   ·
--   case `zero `zero
--   ((μ
--     (ƛ
--      (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
--    · `suc (`suc `zero)
--    ·
--    ((μ
--      (ƛ
--       (ƛ
--        case (` (S Z)) `zero
--        ((μ
--          (ƛ
--           (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
--         · ` (S Z)
--         · (` (S (S (S Z))) · ` Z · ` (S Z))))))
--     · ` Z
--     · `suc (`suc `zero))))
--   —→⟨ ξ-·₂ V-ƛ (ξ-·₂ V-ƛ β-zero) ⟩
--   (ƛ
--   case (`suc (`suc `zero)) (` Z)
--   (`suc
--    ((μ
--      (ƛ
--       (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
--     · ` Z
--     · ` (S Z))))
--   ·
--   ((ƛ
--    case (`suc (`suc `zero)) (` Z)
--    (`suc
--     ((μ
--       (ƛ
--        (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
--      · ` Z
--      · ` (S Z))))
--   · `zero)
--   —→⟨ ξ-·₂ V-ƛ (β-ƛ V-zero) ⟩
--   (ƛ
--   case (`suc (`suc `zero)) (` Z)
--   (`suc
--    ((μ
--      (ƛ
--       (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
--     · ` Z
--     · ` (S Z))))
--   ·
--   case (`suc (`suc `zero)) `zero
--   (`suc
--   ((μ
--     (ƛ
--      (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
--    · ` Z
--    · `zero))
--   —→⟨ ξ-·₂ V-ƛ (β-suc (V-suc V-zero)) ⟩
--   (ƛ
--   case (`suc (`suc `zero)) (` Z)
--   (`suc
--    ((μ
--      (ƛ
--       (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
--     · ` Z
--     · ` (S Z))))
--   ·
--   `suc
--   ((μ
--    (ƛ
--     (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
--   · `suc `zero
--   · `zero)
--   —→⟨ ξ-·₂ V-ƛ (ξ-suc (ξ-·₁ (ξ-·₁ β-μ))) ⟩
--   (ƛ
--   case (`suc (`suc `zero)) (` Z)
--   (`suc
--    ((μ
--      (ƛ
--       (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
--     · ` Z
--     · ` (S Z))))
--   ·
--   `suc
--   ((ƛ
--    (ƛ
--     case (` (S Z)) (` Z)
--     (`suc
--      ((μ
--        (ƛ
--         (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
--       · ` Z
--       · ` (S Z)))))
--   · `suc `zero
--   · `zero)
--   —→⟨ ξ-·₂ V-ƛ (ξ-suc (ξ-·₁ (β-ƛ (V-suc V-zero)))) ⟩
--   (ƛ
--   case (`suc (`suc `zero)) (` Z)
--   (`suc
--    ((μ
--      (ƛ
--       (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
--     · ` Z
--     · ` (S Z))))
--   ·
--   `suc
--   ((ƛ
--    case (`suc `zero) (` Z)
--    (`suc
--     ((μ
--       (ƛ
--        (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
--      · ` Z
--      · ` (S Z))))
--   · `zero)
--   —→⟨ ξ-·₂ V-ƛ (ξ-suc (β-ƛ V-zero)) ⟩
--   (ƛ
--   case (`suc (`suc `zero)) (` Z)
--   (`suc
--    ((μ
--      (ƛ
--       (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
--     · ` Z
--     · ` (S Z))))
--   ·
--   `suc
--   case (`suc `zero) `zero
--   (`suc
--   ((μ
--     (ƛ
--      (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
--    · ` Z
--    · `zero))
--   —→⟨ ξ-·₂ V-ƛ (ξ-suc (β-suc V-zero)) ⟩
--   (ƛ
--   case (`suc (`suc `zero)) (` Z)
--   (`suc
--    ((μ
--      (ƛ
--       (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
--     · ` Z
--     · ` (S Z))))
--   ·
--   `suc
--   (`suc
--   ((μ
--     (ƛ
--      (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
--    · `zero
--    · `zero))
--   —→⟨ ξ-·₂ V-ƛ (ξ-suc (ξ-suc (ξ-·₁ (ξ-·₁ β-μ)))) ⟩
--   (ƛ
--   case (`suc (`suc `zero)) (` Z)
--   (`suc
--    ((μ
--      (ƛ
--       (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
--     · ` Z
--     · ` (S Z))))
--   ·
--   `suc
--   (`suc
--   ((ƛ
--     (ƛ
--      case (` (S Z)) (` Z)
--      (`suc
--       ((μ
--         (ƛ
--          (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
--        · ` Z
--        · ` (S Z)))))
--    · `zero
--    · `zero))
--   —→⟨ ξ-·₂ V-ƛ (ξ-suc (ξ-suc (ξ-·₁ (β-ƛ V-zero)))) ⟩
--   (ƛ
--   case (`suc (`suc `zero)) (` Z)
--   (`suc
--    ((μ
--      (ƛ
--       (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
--     · ` Z
--     · ` (S Z))))
--   ·
--   `suc
--   (`suc
--   ((ƛ
--     case `zero (` Z)
--     (`suc
--      ((μ
--        (ƛ
--         (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
--       · ` Z
--       · ` (S Z))))
--    · `zero))
--   —→⟨ ξ-·₂ V-ƛ (ξ-suc (ξ-suc (β-ƛ V-zero))) ⟩
--   (ƛ
--   case (`suc (`suc `zero)) (` Z)
--   (`suc
--    ((μ
--      (ƛ
--       (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
--     · ` Z
--     · ` (S Z))))
--   ·
--   `suc
--   (`suc
--   case `zero `zero
--   (`suc
--    ((μ
--      (ƛ
--       (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
--     · ` Z
--     · `zero)))
--   —→⟨ ξ-·₂ V-ƛ (ξ-suc (ξ-suc β-zero)) ⟩
--   (ƛ
--   case (`suc (`suc `zero)) (` Z)
--   (`suc
--    ((μ
--      (ƛ
--       (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
--     · ` Z
--     · ` (S Z))))
--   · `suc (`suc `zero)
--   —→⟨ β-ƛ (V-suc (V-suc V-zero)) ⟩
--   case (`suc (`suc `zero)) (`suc (`suc `zero))
--   (`suc
--   ((μ
--     (ƛ
--      (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
--    · ` Z
--    · `suc (`suc `zero)))
--   —→⟨ β-suc (V-suc V-zero) ⟩
--   `suc
--   ((μ
--    (ƛ
--     (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
--   · `suc `zero
--   · `suc (`suc `zero))
--   —→⟨ ξ-suc (ξ-·₁ (ξ-·₁ β-μ)) ⟩
--   `suc
--   ((ƛ
--    (ƛ
--     case (` (S Z)) (` Z)
--     (`suc
--      ((μ
--        (ƛ
--         (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
--       · ` Z
--       · ` (S Z)))))
--   · `suc `zero
--   · `suc (`suc `zero))
--   —→⟨ ξ-suc (ξ-·₁ (β-ƛ (V-suc V-zero))) ⟩
--   `suc
--   ((ƛ
--    case (`suc `zero) (` Z)
--    (`suc
--     ((μ
--       (ƛ
--        (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
--      · ` Z
--      · ` (S Z))))
--   · `suc (`suc `zero))
--   —→⟨ ξ-suc (β-ƛ (V-suc (V-suc V-zero))) ⟩
--   `suc
--   case (`suc `zero) (`suc (`suc `zero))
--   (`suc
--   ((μ
--     (ƛ
--      (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
--    · ` Z
--    · `suc (`suc `zero)))
--   —→⟨ ξ-suc (β-suc V-zero) ⟩
--   `suc
--   (`suc
--   ((μ
--     (ƛ
--      (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
--    · `zero
--    · `suc (`suc `zero)))
--   —→⟨ ξ-suc (ξ-suc (ξ-·₁ (ξ-·₁ β-μ))) ⟩
--   `suc
--   (`suc
--   ((ƛ
--     (ƛ
--      case (` (S Z)) (` Z)
--      (`suc
--       ((μ
--         (ƛ
--          (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
--        · ` Z
--        · ` (S Z)))))
--    · `zero
--    · `suc (`suc `zero)))
--   —→⟨ ξ-suc (ξ-suc (ξ-·₁ (β-ƛ V-zero))) ⟩
--   `suc
--   (`suc
--   ((ƛ
--     case `zero (` Z)
--     (`suc
--      ((μ
--        (ƛ
--         (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
--       · ` Z
--       · ` (S Z))))
--    · `suc (`suc `zero)))
--   —→⟨ ξ-suc (ξ-suc (β-ƛ (V-suc (V-suc V-zero)))) ⟩
--   `suc
--   (`suc
--   case `zero (`suc (`suc `zero))
--   (`suc
--    ((μ
--      (ƛ
--       (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
--     · ` Z
--     · `suc (`suc `zero))))
--   —→⟨ ξ-suc (ξ-suc β-zero) ⟩ `suc (`suc (`suc (`suc `zero))) ∎)
--   (done (V-suc (V-suc (V-suc (V-suc V-zero)))))
-- mul-example = refl
