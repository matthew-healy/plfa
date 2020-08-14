module plfa.part2.Lambda where

open import Data.Bool using (T; not)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; _∷_; [])
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (∃-syntax; _×_) renaming (_,_ to ⟨_,_⟩)
open import Data.String using (String; _≟_)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Nullary.Decidable using (⌊_⌋; False; toWitnessFalse)
open import Relation.Nullary.Negation using (¬?)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong)
open import plfa.part1.Isomorphism using (_≲_; _≃_)

Id : Set
Id = String

infix  5 ƛ_⇒_
infix  5 μ_⇒_
infixl 7 _·_
infix  8 `suc_
infix  9 `_

data Term : Set where
  `_                   : Id → Term
  ƛ_⇒_                 : Id → Term → Term
  _·_                  : Term → Term → Term
  `zero                : Term
  `suc_                : Term → Term
  case_[zero⇒_|suc_⇒_] : Term → Term → Id → Term → Term
  μ_⇒_                 : Id → Term → Term

two : Term
two = `suc `suc `zero

plus : Term
plus = μ "+" ⇒ ƛ "m" ⇒ ƛ "n" ⇒
          case ` "m"
            [zero⇒ ` "n"
            |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n") ]

twoᶜ : Term
twoᶜ = ƛ "s" ⇒ ƛ "z" ⇒ ` "s" · (` "s" · ` "z")

plusᶜ : Term
plusᶜ = ƛ "m" ⇒ ƛ "n" ⇒ ƛ "s" ⇒ ƛ "z" ⇒
        ` "m" · ` "s" · (` "n" · ` "s" · ` "z")

sucᶜ : Term
sucᶜ = ƛ "n" ⇒ `suc (` "n")

-- Exercise: mul
mul : Term
mul = μ "×" ⇒ ƛ "m" ⇒ ƛ "n" ⇒
        case ` "m"
          [zero⇒ `zero
          |suc "m" ⇒ plus · ` "n" · (` "×" · ` "m" · ` "n") ]

-- Exercise: mulᶜ
mulᶜ : Term
mulᶜ = ƛ "m" ⇒ ƛ "n" ⇒ ƛ "s" ⇒ ƛ "z" ⇒
        ` "m" · (` "n" · ` "s") · ` "z"

-- Exercise: primed
ƛ′_⇒_ : Term → Term → Term
ƛ′ (` x) ⇒ N = ƛ x ⇒ N
ƛ′ _ ⇒ _ = ⊥-elim impossible
  where postulate impossible : ⊥

case′_[zero⇒_|suc_⇒_] : Term → Term → Term → Term → Term
case′ L [zero⇒ M |suc (` x) ⇒ N ] = case L [zero⇒ M |suc x ⇒ N ]
case′ _ [zero⇒ _ |suc _ ⇒ _ ]     = ⊥-elim impossible
  where postulate impossible : ⊥

μ′_⇒_ : Term → Term → Term
μ′ (` x) ⇒ N = μ x ⇒ N
μ′ _ ⇒ _     = ⊥-elim impossible
  where postulate impossible : ⊥

plus′ : Term
plus′ = μ′ + ⇒ ƛ′ m ⇒ ƛ′ n ⇒
          case′ m
            [zero⇒ n
            |suc m ⇒ `suc (+ · m · n) ]
  where
  + = ` "+"
  m = ` "m"
  n = ` "n"

mul′ : Term
mul′ = μ′ × ⇒ ƛ′ m ⇒ ƛ′ n ⇒
        case′ m
          [zero⇒ n
          |suc m ⇒ plus′ · n · (× · m · n) ]
  where
  × = ` "×"
  m = ` "m"
  n = ` "n"

-- Bound and free variables

-- ƛ "s" ⇒ ƛ "z" ⇒ ` "s" · (` "s" · ` "z") has both s and z as bound variables.
-- ƛ "z" ⇒ ` "s" · (` "s" · ` "z") has z bound and s free.
-- ` "s" · (` "s" · ` "z") has both s and z as free variables.

-- No free variables: "closed", otherwise "open"

-- Values

data Value : Term → Set where

  V-ƛ : ∀ {x N}
        ---------------
      → Value (ƛ x ⇒ N)

  V-zero :
        -----------
        Value `zero

  V-suc : ∀ {V}
    → Value V
      --------------
    → Value (`suc V)

-- Substitution
infix 9 _[_:=_]

_[_:=_] : Term → Id → Term → Term
(` x) [ y := V ] with x ≟ y
... | yes _         = V
... | no  _         = ` x
(ƛ x ⇒ N) [ y := V ] with x ≟ y
... | yes _         = ƛ x ⇒ N
... | no  _         = ƛ x ⇒ N [ y := V ]
(L · M) [ y := V ]  = L [ y := V ] · M [ y := V ]
(`zero) [ y := V ]  = `zero
(`suc M) [ y := V ] = `suc M [ y := V ]
(case L [zero⇒ M |suc x ⇒ N ]) [ y := V ] with x ≟ y
... | yes _         = case L [ y := V ] [zero⇒ M [ y := V ] |suc x ⇒ N ]
... | no  _         = case L [ y := V ] [zero⇒ M [ y := V ] |suc x ⇒ N [ y := V ] ]
(μ x ⇒ N) [ y := V ] with x ≟ y
... | yes _         = μ x ⇒ N
... | no  _         = μ x ⇒ N [ y := V ]

-- Examples
_ : (ƛ "z" ⇒ ` "s" · (` "s" · ` "z")) [ "s" := sucᶜ ] ≡ ƛ "z" ⇒ sucᶜ · (sucᶜ · ` "z")
_ = refl

_ : (sucᶜ · (sucᶜ · ` "z")) [ "z" := `zero ] ≡ sucᶜ · (sucᶜ · `zero)
_ = refl

_ : (ƛ "x" ⇒ ` "y") [ "y" := `zero ] ≡ ƛ "x" ⇒ `zero
_ = refl

_ : (ƛ "x" ⇒ ` "x") ["x" := `zero ] ≡ ƛ "x" ⇒ ` "x"
_ = refl

_ : (ƛ "y" ⇒ ` "y") [ "x" := `zero ] ≡ ƛ "y" ⇒ ` "y"
_ = refl

-- Quiz
_ : (ƛ "y" ⇒ ` "x" · (ƛ "x" ⇒ ` "x")) [ "x" := `zero ] ≡ (ƛ "y" ⇒ `zero · (ƛ "x" ⇒ ` "x"))
_ = refl

-- Exercise: _[_:=_]′
_[_:=_]′ : Term → Id → Term → Term
replaceIfEqual : (x y : Id) → (Term → Term) → Term → Term → Term

-- These are the same as before
(` x) [ y := V ]′ with x ≟ y
... | yes _ = V
... | no  _ = ` x
(L · M) [ y := V ]′  = L [ y := V ] · M [ y := V ]
(`zero) [ y := V ]′  = `zero
(`suc M) [ y := V ]′ = `suc M [ y := V ]

-- These call replaceIfEqual with the Ids to compare, a function which computes the whole term,
-- the term to (potentially) apply replacement to, and the value we'll replace y by.
(ƛ x ⇒ N) [ y := V ]′                      = replaceIfEqual x y (λ N → ƛ x ⇒ N) N V
(case L [zero⇒ M |suc x ⇒ N ]) [ y := V ]′ = replaceIfEqual x y (λ N → case L [ y := V ] [zero⇒ M [ y := V ] |suc x ⇒ N ]) N V
(μ x ⇒ N) [ y := V ]′                      = replaceIfEqual x y (λ N → μ x ⇒ N) N V

replaceIfEqual x y Term→Term N V with x ≟ y
... | yes _ = Term→Term N
... | no  _ = Term→Term (N [ y := V ]′)

-- Test:
_ : (ƛ "z" ⇒ ` "s" · (` "s" · ` "z")) [ "s" := sucᶜ ]′ ≡ ƛ "z" ⇒ sucᶜ · (sucᶜ · ` "z")
_ = refl

_ : (sucᶜ · (sucᶜ · ` "z")) [ "z" := `zero ]′ ≡ sucᶜ · (sucᶜ · `zero)
_ = refl
-- It works!

-- Reduction
infix 4 _—→_

data _—→_ : Term → Term → Set where

  ξ-·₁ : ∀ {L L′ M}
    → L —→ L′
      ---------------
    → L · M —→ L′ · M

  ξ-·₂ : ∀ {V M M′}
    → Value V
    → M —→ M′
      ---------------
    → V · M —→ V · M′

  β-ƛ : ∀ {x N V}
    → Value V
      -----------------------------
    → (ƛ x ⇒ N) · V —→ N [ x := V ]

  ξ-suc : ∀ {M M′}
    → M —→ M′
      -----------------
    → `suc M —→ `suc M′

  ξ-case : ∀ {x L L′ M N}
    → L —→ L′
      --------------------------------------------------------------
    → case L [zero⇒ M |suc x ⇒ N ] —→ case L′ [zero⇒ M |suc x ⇒ N ]

  β-zero : ∀ {x M N}
      -------------------------------------
    → case `zero [zero⇒ M |suc x ⇒ N ] —→ M

  β-suc : ∀ {x V M N}
    → Value V
      -------------------------------------------------
    → case `suc V [zero⇒ M |suc x ⇒ N ] —→ N [ x := V ]

  β-μ : ∀ {x M}
      -----------------------------
    → μ x ⇒ M —→ M [ x := μ x ⇒ M ]

-- Quiz
_ : (ƛ "x" ⇒ ` "x") · (ƛ "x" ⇒ ` "x") —→ (ƛ "x" ⇒ ` "x")
_ = β-ƛ V-ƛ

_ : (ƛ "x" ⇒ ` "x") · (ƛ "x" ⇒ ` "x") · (ƛ "x" ⇒ ` "x")  —→ (ƛ "x" ⇒ ` "x") · (ƛ "x" ⇒ ` "x")
_ = ξ-·₁ (β-ƛ V-ƛ)

_ : twoᶜ · sucᶜ · `zero —→ (ƛ "z" ⇒ sucᶜ · (sucᶜ · ` "z")) · `zero
_ = ξ-·₁ (β-ƛ V-ƛ)

-- Reflexive and transitive closure
infix  2 _—↠_
infix  1 begin_
infixr 2 _—→⟨_⟩_
infix  3 _∎

data _—↠_ : Term → Term → Set where
  _∎ : ∀ M
      ------
    → M —↠ M

  _—→⟨_⟩_ : ∀ L {M N}
    → L —→ M
    → M —↠ N
      ------
    → L —↠ N

begin_ : ∀ {M N}
  → M —↠ N
    ------
  → M —↠ N
begin M—↠N = M—↠N

-- Alternative definition
data _—↠′_ : Term → Term → Set where
  step′ : ∀ {M N}
    → M —→ N
      -------
    → M —↠′ N

  refl′ : ∀ {M}
      -------
    → M —↠′ M

  trans′ : ∀ {L M N}
    → L —↠′ M
    → M —↠′ N
      -------
    → L —↠′ N

-- Exercise: —↠≲—↠′
—↠-trans : ∀ L {M N : Term}
  → L —↠ M
  → M —↠ N
    ------
  → L —↠ N
—↠-trans L (L ∎) L↠N = L↠N
—↠-trans L (_—→⟨_⟩_ L {P} L→P P↠M) M↠N = L —→⟨ L→P ⟩ (—↠-trans P P↠M M↠N)

—↠≲—↠′ : ∀ {M N : Term} → M —↠ N ≲ M —↠′ N
—↠≲—↠′ = record
  { to      = to
  ; from    = from
  ; from∘to = from∘to
  }
  where
    to : ∀ {M N : Term} → M —↠ N → M —↠′ N
    to (M ∎) = refl′
    to (M —→⟨ M→N ⟩ N↠O) = trans′ (step′ M→N) (to N↠O)

    from : ∀ {M N : Term} → M —↠′ N → M —↠ N
    from {M} {N} (step′ M→N) = M —→⟨ M→N ⟩ N ∎
    from {M} refl′ = M ∎
    from {M} (trans′ M↠′N N↠′O) = —↠-trans M (from M↠′N) (from N↠′O)

    from∘to : ∀ {M N : Term} (M↠N : M —↠ N) → from (to M↠N) ≡ M↠N
    from∘to (M ∎) = refl
    from∘to (M —→⟨ M→L ⟩ L↠N) = cong (λ x → M —→⟨ M→L ⟩ x) (from∘to L↠N)

-- Confluence
-- If term L reduces to two other terms M and N, then both M and N reduce to some P,
postulate
  confluence : ∀ {L M N}
    → ((L —↠ M) × (L —↠ N))
      ----------------------------
    → ∃[ P ] ((M —↠ P) × (N —↠ P))

-- If L reduces to M and N by a single step, we call this the diamond property.
  diamond : ∀ {L M N}
    → ((L —→ M) × (L —→ N))
      ----------------------------
    → ∃[ P ] ((M —↠ P) × (N —↠ P))

-- "The reduction system studied in this chapter is deterministic."
postulate
  deterministic : ∀ {L M N}
    → L —→ M
    → L —→ N
      ------
    → M ≡ N

-- "Every deterministic relationship satisfies confluence and the diamond property."

-- Examples
_ : twoᶜ · sucᶜ · `zero —↠ `suc `suc `zero
_ = begin
      twoᶜ · sucᶜ · `zero
    —→⟨ ξ-·₁ (β-ƛ V-ƛ) ⟩
      (ƛ "z" ⇒ sucᶜ · (sucᶜ · ` "z")) · `zero
    —→⟨ β-ƛ V-zero ⟩
      sucᶜ · (sucᶜ · `zero)
    —→⟨ ξ-·₂ V-ƛ (β-ƛ V-zero) ⟩
      sucᶜ · `suc `zero
    —→⟨ β-ƛ (V-suc V-zero) ⟩
      `suc `suc `zero
    ∎

one : Term
one = `suc `zero

oneᶜ : Term
oneᶜ = ƛ "s" ⇒ ƛ "z" ⇒ ` "s" · ` "z"

-- Exercise: plus-example
_ : plus · one · one —↠ `suc `suc `zero
_ =
  begin
    plus · one · one
  —→⟨ ξ-·₁ (ξ-·₁ β-μ) ⟩
    (ƛ "m" ⇒ ƛ "n" ⇒
      case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (plus · ` "m" · ` "n") ])
      · one · one
  —→⟨ ξ-·₁ (β-ƛ (V-suc V-zero)) ⟩
    (ƛ "n" ⇒
      case one [zero⇒ ` "n" |suc "m" ⇒ `suc (plus · ` "m" · ` "n") ])
      · one
  —→⟨ β-ƛ (V-suc V-zero) ⟩
    case one [zero⇒ one |suc "m" ⇒ `suc (plus · ` "m" · one)]
  —→⟨ β-suc V-zero ⟩
    `suc (plus · `zero · one)
  —→⟨ ξ-suc (ξ-·₁ (ξ-·₁ β-μ)) ⟩
    `suc ((ƛ "m" ⇒ ƛ "n" ⇒
      case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (plus · ` "m" · ` "n") ])
      · `zero · one)
   —→⟨ ξ-suc (ξ-·₁ (β-ƛ V-zero)) ⟩
    `suc ((ƛ "n" ⇒
      case `zero [zero⇒ ` "n" |suc "m" ⇒ `suc (plus · ` "m" · ` "n")])
      · one)
   —→⟨ ξ-suc (β-ƛ (V-suc V-zero)) ⟩
    `suc (case `zero [zero⇒ one |suc "m" ⇒ `suc (plus · ` "m" · one)])
   —→⟨ ξ-suc β-zero ⟩
    `suc `suc `zero
   ∎

 -- plusᶜ : Term
 -- plusᶜ = ƛ "m" ⇒ ƛ "n" ⇒ ƛ "s" ⇒ ƛ "z" ⇒
 --         ` "m" · ` "s" · (` "n" · ` "s" · ` "z")

_ : plusᶜ · oneᶜ · oneᶜ · sucᶜ · `zero —↠ `suc `suc `zero
_ =
  begin
    (ƛ "m" ⇒ ƛ "n" ⇒ ƛ "s" ⇒ ƛ "z" ⇒ ` "m" · ` "s" · (` "n" · ` "s" · ` "z"))
      · oneᶜ · oneᶜ · sucᶜ · `zero
  —→⟨ ξ-·₁ (ξ-·₁ (ξ-·₁ (β-ƛ V-ƛ))) ⟩
    (ƛ "n" ⇒ ƛ "s" ⇒ ƛ "z" ⇒ oneᶜ · ` "s" · (` "n" · ` "s" · ` "z"))
      · oneᶜ · sucᶜ · `zero
  —→⟨ ξ-·₁ (ξ-·₁ (β-ƛ V-ƛ)) ⟩
    (ƛ "s" ⇒ ƛ "z" ⇒ oneᶜ · ` "s" · (oneᶜ · ` "s" · ` "z"))
      · sucᶜ · `zero
  —→⟨ ξ-·₁ (β-ƛ V-ƛ) ⟩
    (ƛ "z" ⇒ oneᶜ · sucᶜ · (oneᶜ · sucᶜ · ` "z")) · `zero
  —→⟨ β-ƛ V-zero ⟩
    (ƛ "s" ⇒ ƛ "z" ⇒ ` "s" · ` "z") · sucᶜ · (oneᶜ · sucᶜ · `zero)
  —→⟨ ξ-·₁ (β-ƛ V-ƛ) ⟩
    (ƛ "z" ⇒ sucᶜ · ` "z") · ((ƛ "s" ⇒ ƛ "z" ⇒ ` "s" · ` "z") · sucᶜ · `zero)
  —→⟨ ξ-·₂ V-ƛ (ξ-·₁ (β-ƛ V-ƛ)) ⟩
    (ƛ "z" ⇒ sucᶜ · ` "z") · ((ƛ "z" ⇒ sucᶜ · ` "z") · `zero)
  —→⟨ ξ-·₂ V-ƛ (β-ƛ V-zero) ⟩
    (ƛ "z" ⇒ sucᶜ · ` "z") · (sucᶜ · `zero)
  —→⟨ ξ-·₂ V-ƛ (β-ƛ V-zero) ⟩
    (ƛ "z" ⇒ sucᶜ · ` "z") · (`suc `zero)
  —→⟨ β-ƛ (V-suc V-zero) ⟩
    sucᶜ · (`suc `zero)
  —→⟨ β-ƛ (V-suc V-zero) ⟩
    `suc `suc `zero
  ∎

-- Syntax of types

infixr 7 _⇒_

data Type : Set where
  _⇒_ : Type → Type → Type
  `ℕ  : Type

-- Quiz
-- ƛ "s" ⇒ ` "s" · (` "s"  · `zero) has type (`ℕ ⇒ `ℕ) ⇒ `ℕ
-- (ƛ "s" ⇒ ` "s" · (` "s"  · `zero)) · sucᶜ has type `ℕ

-- Typing

-- Contexts
infixl 5 _,_⦂_

data Context : Set where
  ∅     : Context
  _,_⦂_ : Context → Id → Type → Context

-- Exercise: Context-≃
Context-≃ : Context ≃ List(Id × Type)
Context-≃ = record
  {      to = to
  ;    from = from
  ; from∘to = from∘to
  ; to∘from = to∘from
  }
  where

    to : Context → List(Id × Type)
    to ∅ = []
    to (c , x ⦂ A) = ⟨ x , A ⟩ ∷ to c

    from : List(Id × Type) → Context
    from [] = ∅
    from (⟨ x , A ⟩ ∷ l) = (from l) , x ⦂ A

    from∘to : ∀ (c : Context) → from (to c) ≡ c
    from∘to ∅ = refl
    from∘to (c , x ⦂ A) = cong (_, x ⦂ A) (from∘to c)

    to∘from : ∀ (l : List(Id × Type)) → to (from l) ≡ l
    to∘from [] = refl
    to∘from (⟨ x , A ⟩ ∷ l) = cong (⟨ x , A ⟩ ∷_) (to∘from l)

-- Lookup judgement

infix 4 _∋_⦂_

data _∋_⦂_ : Context → Id → Type → Set where
  Z : ∀ {Γ x A}
      -----------------
    → Γ , x ⦂ A ∋ x ⦂ A

  S : ∀ {Γ x y A B}
    → x ≢ y             -- prevents a single value having two different types
    → Γ ∋ x ⦂ A         -- ensures x : A in Γ
      -----------------
    → Γ , y ⦂ B ∋ x ⦂ A -- guarantees that x : A in any extension of Γ by any y : B

_ : ∅ , "x" ⦂ `ℕ ⇒ `ℕ , "y" ⦂ `ℕ , "z" ⦂ `ℕ ∋ "x" ⦂ `ℕ ⇒ `ℕ
_ = S (λ ()) (S (λ ()) Z)

S′ : ∀ {Γ x y A B}
    → {x≢y : False (x ≟ y)}
    → Γ ∋ x ⦂ A
      ---------------------
    → Γ , y ⦂ B ∋ x ⦂ A
S′ {x≢y = x≢y} x = S (toWitnessFalse x≢y) x

-- Typing judgement
infix 4 _⊢_⦂_

data _⊢_⦂_ : Context → Term → Type → Set where
  -- Axiom
  ⊢` : ∀ {Γ x A}
    → Γ ∋ x ⦂ A
      -----------
    → Γ ⊢ ` x ⦂ A

  -- ⇒-I
  ⊢ƛ : ∀ {Γ x N A B}
    → Γ , x ⦂ A ⊢ N ⦂ B
      -------------------
    → Γ ⊢ ƛ x ⇒ N ⦂ A ⇒ B

  -- ⇒-E
  _·_ : ∀ {Γ L M A B}
    → Γ ⊢ L ⦂ A ⇒ B
    → Γ ⊢ M ⦂ A
      -------------
    → Γ ⊢ L · M ⦂ B

  -- ℕ-I₁
  ⊢zero : ∀ {Γ}
      --------------
    → Γ ⊢ `zero ⦂ `ℕ

  -- ℕ-I₂
  ⊢suc : ∀ {Γ M}
    → Γ ⊢ M ⦂ `ℕ
      ---------------
    → Γ ⊢ `suc M ⦂ `ℕ

  -- ℕ-E
  ⊢case : ∀ {Γ L M x N A}
    → Γ ⊢ L ⦂ `ℕ
    → Γ ⊢ M ⦂ A
    → Γ , x ⦂ `ℕ ⊢ N ⦂ A
      ------------------------------------
    → Γ ⊢ case L [zero⇒ M |suc x ⇒ N ] ⦂ A

  ⊢μ : ∀ {Γ x M A}
    → Γ , x ⦂ A ⊢ M ⦂ A
      -----------------
    → Γ ⊢ μ x ⇒ M ⦂ A

-- Example type derivations
Ch : Type → Type
Ch A = (A ⇒ A) ⇒ A ⇒ A

⊢twoᶜ : ∀ {Γ A} → Γ ⊢ twoᶜ ⦂ Ch A
⊢twoᶜ = ⊢ƛ (⊢ƛ ((⊢` ∋s) · ((⊢` ∋s ) · ⊢` ∋z)))
  where
  ∋s = S′ Z
  ∋z = Z

⊢two : ∀ {Γ} → Γ ⊢ two ⦂ `ℕ
⊢two = ⊢suc (⊢suc ⊢zero)

⊢plus : ∀ {Γ} → Γ ⊢ plus ⦂ `ℕ ⇒ `ℕ ⇒ `ℕ
⊢plus = ⊢μ (⊢ƛ (⊢ƛ (⊢case (⊢` ∋m) (⊢` ∋n)
          (⊢suc ((⊢` ∋+) · (⊢` ∋m′) · ⊢` ∋n′)))))
  where
  ∋+  = S′ (S′ (S′ Z))
  ∋m  = S′ Z
  ∋n  = Z
  ∋m′ = Z
  ∋n′ = S′ Z

⊢2+2 : ∅ ⊢ plus · two · two ⦂ `ℕ
⊢2+2 = ⊢plus · ⊢two · ⊢two

⊢plusᶜ : ∀ {Γ A} → Γ  ⊢ plusᶜ ⦂ Ch A ⇒ Ch A ⇒ Ch A
⊢plusᶜ = ⊢ƛ (⊢ƛ (⊢ƛ (⊢ƛ (⊢` ∋m · ⊢` ∋s · (⊢` ∋n · ⊢` ∋s · ⊢` ∋z)))))
  where
  ∋m = S′ (S′ (S′ Z))
  ∋n = S′ (S′ Z)
  ∋s = S′ Z
  ∋z = Z

⊢sucᶜ : ∀ {Γ} → Γ ⊢ sucᶜ ⦂ `ℕ ⇒ `ℕ
⊢sucᶜ = ⊢ƛ (⊢suc (⊢` ∋n))
  where
  ∋n = Z

⊢2+2ᶜ : ∅ ⊢ plusᶜ · twoᶜ · twoᶜ · sucᶜ · `zero ⦂ `ℕ
⊢2+2ᶜ = ⊢plusᶜ · ⊢twoᶜ · ⊢twoᶜ · ⊢sucᶜ · ⊢zero

-- Lookup is injective
∋-injective : ∀ {Γ x A B} → Γ ∋ x ⦂ A → Γ ∋ x ⦂ B → A ≡ B
∋-injective Z            Z          = refl
∋-injective Z            (S x≢x _)  = ⊥-elim (x≢x refl)
∋-injective (S x≢x _)    Z          = ⊥-elim (x≢x refl)
∋-injective (S _ Γ∋x⦂A) (S _ Γ∋x⦂B) = ∋-injective Γ∋x⦂A Γ∋x⦂B

-- Non-examples

nope₁ : ∀ {A} → ¬ (∅ ⊢ `zero · `suc `zero ⦂ A)
nope₁ (() · _)

nope₂ : ∀ {A} → ¬ (∅ ⊢ ƛ "x" ⇒ ` "x" · ` "x" ⦂ A)
nope₂ (⊢ƛ (⊢` ∋x · ⊢` ∋x′)) = contradiction (∋-injective ∋x ∋x′)
  where
  contradiction : ∀ {A B} → ¬ (A ⇒ B ≡ A)
  contradiction ()

-- Quiz

-- ∅ , "y" ⦂ `ℕ ⇒ `ℕ , "x" ⦂ `ℕ ⊢ ` "y" · ` "x" ⦂ A is derivable for A = `ℕ
-- ∅ , "y" ⦂ `ℕ ⇒ `ℕ , "x" ⦂ `ℕ ⊢ ` "x" · ` "y" ⦂ A is not derivable for any A, since "x" ⦂ ℕ means that ` "x" · ` "y" is invalid for any "y".
-- ∅ , "y" ⦂ `ℕ ⇒ `ℕ ⊢ ƛ "x" ⇒ ` "y" · ` "x" ⦂ A is derivable for A = `ℕ ⇒ `ℕ

-- ∅ , "x" ⦂ A ⊢ ` "x" · ` "x" ⦂ B
-- is not derivable for any A or B (I think). A would need to be a function type
-- which had its own type as the type of its argument. Say it was C ⇒ D, but then
-- it must have type (C ⇒ D) ⇒ D but C ⇒ D is not C, so we have a contradiction.


-- ∅ , "x" ⦂ A , "y" ⦂ B ⊢ ƛ "z" ⇒ ` "x" · (` "y" · ` "z") ⦂ C
-- is derivable for A = `ℕ ⇒ `ℕ, B = `ℕ ⇒ `ℕ, C = `ℕ ⇒ `ℕ

-- Exercise: ⊢mul
⊢mul : ∀ {Γ} → Γ ⊢ mul ⦂ `ℕ ⇒ `ℕ ⇒ `ℕ
⊢mul = ⊢μ (⊢ƛ (⊢ƛ (⊢case (⊢` ∋m) ⊢zero
        (⊢plus · (⊢` ∋m′) · ((⊢` ∋×) · ⊢` ∋n · ⊢` ∋n′)))))
  where
  ∋×  = S′ (S′ (S′ Z))
  ∋m  = S′ Z
  ∋n  = Z
  ∋m′ = S′ Z
  ∋n′ = S′ Z

-- Exercise: ⊢mulᶜ
⊢mulᶜ : ∀ {Γ A} → Γ ⊢ mulᶜ ⦂ Ch A ⇒ Ch A ⇒ Ch A
⊢mulᶜ = ⊢ƛ (⊢ƛ (⊢ƛ (⊢ƛ (⊢` ∋m · ((⊢` ∋n) · ⊢` ∋s) · ⊢` ∋z))))
  where
  ∋m = S′ (S′ (S′ Z))
  ∋n = S′ (S′ Z)
  ∋s = S′ Z
  ∋z = Z
