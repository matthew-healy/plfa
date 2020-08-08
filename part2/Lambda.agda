module plfa.part2.Lambda where

open import Data.Bool using (T; not)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; _∷_; [])
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (∃-syntax; _×_)
open import Data.String using (String; _≟_)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Nullary.Decidable using (⌊_⌋; False; toWitnessFalse)
open import Relation.Nullary.Negation using (¬?)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)

Id : Set
Id = String

infix  5 ƛ_⇒_
infix  5 μ_⇒_
infixl 7 _∙_
infix  8 ‵suc_
infix  9 ‵_

data Term : Set where
  ‵_                   : Id → Term
  ƛ_⇒_                 : Id → Term → Term
  _∙_                  : Term → Term → Term
  ‵zero                : Term
  ‵suc_                : Term → Term
  case_[zero⇒_|suc_⇒_] : Term → Term → Id → Term → Term
  μ_⇒_                 : Id → Term → Term

two : Term
two = ‵suc ‵suc ‵zero

plus : Term
plus = μ "+" ⇒ ƛ "m" ⇒ ƛ "n" ⇒
          case ‵ "m"
            [zero⇒ ‵ "n"
            |suc "m" ⇒ ‵suc (‵ "+" ∙ ‵ "m" ∙ ‵ "n") ]

twoᶜ : Term
twoᶜ = ƛ "s" ⇒ ƛ "z" ⇒ ‵ "s" ∙ (‵ "s" ∙ ‵ "z")

plusᶜ : Term
plusᶜ = ƛ "m" ⇒ ƛ "n" ⇒ ƛ "s" ⇒ ƛ "z" ⇒
        ‵ "m" ∙ ‵ "s" ∙ (‵ "n" ∙ ‵ "s" ∙ ‵ "z")

sucᶜ : Term
sucᶜ = ƛ "n" ⇒ ‵suc (‵ "n")

-- Exercise: mul
mul : Term
mul = μ "×" ⇒ ƛ "m" ⇒ ƛ "n" ⇒
        case ‵ "m"
          [zero⇒ ‵zero
          |suc "m" ⇒ plus ∙ ‵ "n" ∙ (‵ "×" ∙ ‵ "m" ∙ ‵ "n") ]

-- Exercise: mulᶜ
mulᶜ : Term
mulᶜ = ƛ "m" ⇒ ƛ "n" ⇒ ƛ "s" ⇒ ƛ "z" ⇒
        ‵ "m" ∙ (‵ "n" ∙ ‵ "s") ∙ ‵ "z"

-- Exercise: primed
ƛ′_⇒_ : Term → Term → Term
ƛ′ (‵ x) ⇒ N = ƛ x ⇒ N
ƛ′ _ ⇒ _ = ⊥-elim impossible
  where postulate impossible : ⊥

case′_[zero⇒_|suc_⇒_] : Term → Term → Term → Term → Term
case′ L [zero⇒ M |suc (‵ x) ⇒ N ] = case L [zero⇒ M |suc x ⇒ N ]
case′ _ [zero⇒ _ |suc _ ⇒ _ ]     = ⊥-elim impossible
  where postulate impossible : ⊥

μ′_⇒_ : Term → Term → Term
μ′ (‵ x) ⇒ N = μ x ⇒ N
μ′ _ ⇒ _     = ⊥-elim impossible
  where postulate impossible : ⊥

plus′ : Term
plus′ = μ′ + ⇒ ƛ′ m ⇒ ƛ′ n ⇒
          case′ m
            [zero⇒ n
            |suc m ⇒ ‵suc (+ ∙ m ∙ n) ]
  where
  + = ‵ "+"
  m = ‵ "m"
  n = ‵ "n"

mul′ : Term
mul′ = μ′ × ⇒ ƛ′ m ⇒ ƛ′ n ⇒
        case′ m
          [zero⇒ n
          |suc m ⇒ plus′ ∙ n ∙ (× ∙ m ∙ n) ]
  where
  × = ‵ "×"
  m = ‵ "m"
  n = ‵ "n"
