module plfa.part1.QuantifiersBinIsomorphism where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Data.Product using (_×_; proj₁; proj₂; ∃; ∃-syntax) renaming (_,_ to ⟨_,_⟩)
open import plfa.part1.Isomorphism using (_≃_; extensionality)

data Bin : Set where
  ⟨⟩ : Bin
  _O : Bin → Bin
  _I : Bin → Bin

inc : Bin → Bin
inc ⟨⟩ = ⟨⟩ I
inc (b O) = (b I)
inc (b I) = (inc b) O

to : ℕ → Bin
to zero = ⟨⟩ O
to (suc n) = inc (to n)

from : Bin → ℕ
from ⟨⟩    = zero
from (n O) = 2 * (from n)
from (n I) = 1 + 2 * (from n)

data One : Bin → Set where

  ⟨⟩I :
      ----------
      One (⟨⟩ I)

  _O : ∀ { b : Bin }
    → One b
      ---------
    → One (b O)

  _I : ∀ { b : Bin }
    → One b
      ---------
    → One (b I)

data Can : Bin → Set where

  zero :
      ----------
      Can (⟨⟩ O)

  leading-one : ∀ { b : Bin }
    → One b
      -----
    → Can b

postulate
  from-to-inverse : ∀ (n : ℕ) → from (to n) ≡ n -- Proved in Induction chapter
  to-can : ∀ (n : ℕ) → Can (to n) -- Proved in Relations chatper
  can-id : ∀ { b : Bin } → Can b → to (from b) ≡ b -- Proved in Relations chapter

≡One : ∀ {b : Bin} (o o′ : One b) → o ≡ o′
≡One ⟨⟩I ⟨⟩I = refl
≡One (o O) (o′ O) = cong _O (≡One o o′)
≡One (o I) (o′ I) = cong _I (≡One o o′)

≡Can : ∀ {b : Bin} (cb cb′ : Can b) → cb ≡ cb′
≡Can zero (leading-one (() O))
≡Can (leading-one (() O)) zero
≡Can zero zero = refl
≡Can (leading-one o) (leading-one o′) = cong leading-one (≡One o o′)

proj₁≡→Can≡ : {cb cb′ : ∃[ b ](Can b)} → proj₁ cb ≡ proj₁ cb′ → cb ≡ cb′
proj₁≡→Can≡ {⟨ b , cb ⟩} {⟨ b , cb′ ⟩} refl = cong (λ{ x → ⟨ b , x ⟩ }) (≡Can cb cb′)

ℕ≃∃Can : ℕ ≃ (∃[ b ] (Can b))
ℕ≃∃Can = record
  { to = λ{ n → ⟨ (to n) , to-can n ⟩ }
  ; from = λ{ ⟨ b , cb ⟩ → from b }
  ; from∘to = from-to-inverse
  ; to∘from = λ{ ⟨ b , cb ⟩ → proj₁≡→Can≡ (can-id cb) }
  }
