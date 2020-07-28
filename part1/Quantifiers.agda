module plfa.part1.Quantifiers where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _≤_; z≤n; s≤s; _∸_)
open import Data.Nat.Properties using (+-assoc; +-identityʳ; +-mono-≤; +-comm)
open import Relation.Nullary using (¬_)
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import plfa.part1.Isomorphism using (_≃_; extensionality)

∀-elim : ∀ {A : Set} {B : A → Set}
  → (L : ∀ (x : A) → B x)
  → (M : A)
    -------
  → B M
∀-elim L M = L M

-- Exercise: ∀-distrib-×

∀-distrib-× : ∀ {A : Set} {B C : A → Set} →
  (∀ (x : A) → B x × C x) ≃ (∀ (x : A) → B x) × (∀ (x : A) → C x)
∀-distrib-× = record
 { to = λ{ f → ⟨ (λ { x → proj₁ (f x) }) , (λ{ x → proj₂ (f x) }) ⟩ }
 ; from = λ{ ⟨ g₁ , g₂ ⟩ x → ⟨ g₁ x , g₂ x ⟩ }
 ; from∘to = λ{ x → refl }
 ; to∘from = λ{ y → refl }
 }

-- Exercise: ⊎∀-implies-∀⊎
⊎∀-implies-∀⊎ : ∀ {A : Set} {B C : A → Set} →
  (∀ (x : A) → B x) ⊎ (∀ (x : A) → C x) → ∀ (x : A) → B x ⊎ C x
⊎∀-implies-∀⊎ = λ{ (inj₁ f[A→B]) x → inj₁ (f[A→B] x)
                 ; (inj₂ g[A→C]) x → inj₂ (g[A→C] x)
                 }

-- Exercise: ∀-×
data Tri : Set where
  aa : Tri
  bb : Tri
  cc : Tri

postulate -- A version of extensionality that works for dependent functions
  extensionality′ : ∀ {A : Set} {B : A → Set} {f g : (x : A) → B x}
    → (∀ (x : A) → f x ≡ g x)
      ---------------------------------
    → f ≡ g

∀-× : ∀ {B : Tri → Set} → (∀ (x : Tri) → B x) ≃ (B aa × B bb × B cc)
∀-× = record
  { to      = λ{ f → ⟨ f aa , ⟨ f bb , f cc ⟩ ⟩ }
  ; from    = λ{ ⟨ baa , ⟨ bbb , bcc ⟩ ⟩ aa → baa
               ; ⟨ baa , ⟨ bbb , bcc ⟩ ⟩ bb → bbb
               ; ⟨ baa , ⟨ bbb , bcc ⟩ ⟩ cc → bcc
               }
  ; from∘to = λ{ f → extensionality′ λ{ aa → refl
                                      ; bb → refl
                                      ; cc → refl
                                      }}
  ; to∘from = λ{ ⟨ baa , ⟨ bbb , bcc ⟩ ⟩ → refl }
  }

-- Existentials

data ∑ (A : Set) (B : A → Set) : Set where
  ⟨_,_⟩ : (x : A) → B x → ∑ A B

∑-syntax = ∑
infix 2 ∑-syntax
syntax ∑-syntax A (λ x → B) = ∑[ x ∈ A ] B

-- Could also declare as a record type
record ∑′ (A : Set) (B : A → Set) : Set where
  field
    proj₁′ : A
    proj₂′ : B proj₁′

-- Can also use ∃
∃ : ∀ {A : Set} (B : A → Set) → Set
∃ {A} B = ∑ A B

∃-syntax = ∃
syntax ∃-syntax (λ x → B) = ∃[ x ] B

∃-elim : ∀ {A : Set} {B : A → Set} {C : Set}
  → (∀ x → B x → C)
  → ∃[ x ] B x
    ---------------
  → C
∃-elim f ⟨ x , y ⟩ = f x y

∀∃-currying : ∀ {A : Set} {B : A → Set} {C : Set}
  → (∀ x → B x → C) ≃ (∃[ x ] B x → C)
∀∃-currying = record
  { to      = λ{ f[x→Bx→C] ⟨ x , Bx ⟩ → f[x→Bx→C] x Bx }
  ; from    = λ{ ∃B→C x Bx → ∃B→C ⟨ x , Bx ⟩ }
  ; from∘to = λ{ f[x→Bx→C] → refl }
  ; to∘from = λ{ ∃B→C → extensionality (λ{ ⟨ x , Bx ⟩ → refl }) }
  }

-- Exercise: ∃-distrib-⊎
∃-distrib-⊎ : ∀ {A : Set} {B C : A → Set}
  → ∃[ x ] (B x ⊎ C x) ≃ (∃[ x ] B x) ⊎ (∃[ x ] C x)
∃-distrib-⊎ = record
  { to      = λ{ ⟨ x , inj₁ Bx ⟩ → inj₁ ⟨ x , Bx ⟩
               ; ⟨ x , inj₂ Cx ⟩ → inj₂ ⟨ x , Cx ⟩
               }
  ; from    = λ{ (inj₁ ⟨ x , Bx ⟩) → ⟨ x , inj₁ Bx ⟩
               ; (inj₂ ⟨ x , Cx ⟩) → ⟨ x , inj₂ Cx ⟩
               }
  ; from∘to = λ{ ⟨ x , inj₁ Bx ⟩ → refl
               ; ⟨ x , inj₂ Cx ⟩ → refl
               }
  ; to∘from = λ{ (inj₁ ⟨ x , Bx ⟩) → refl
               ; (inj₂ ⟨ x , Cx ⟩) → refl
               }
  }

-- Exercise: ∃×-implies-×∃
∃×-implies-×∃ : ∀ {A : Set} {B C : A → Set}
  → ∃[ x ] (B x × C x) → (∃[ x ] B x) × (∃[ x ] C x)
∃×-implies-×∃ = λ{ ⟨ x , ⟨ Bx , Cx ⟩ ⟩ → ⟨ ⟨ x , Bx ⟩ , ⟨ x , Cx ⟩ ⟩ }

-- Exercise: ∃-⊎
∃-⊎ : ∀ {B : Tri → Set} → ∃[ x ] B x ≃ B aa ⊎ B bb ⊎ B cc
∃-⊎ = record
  { to      = λ{ ⟨ aa , Baa ⟩ → inj₁ Baa
               ; ⟨ bb , Bbb ⟩ → inj₂ (inj₁ Bbb)
               ; ⟨ cc , Bcc ⟩ → inj₂ (inj₂ Bcc)
               }
  ; from    = λ{ (inj₁ Baa)        → ⟨ aa , Baa ⟩
               ; (inj₂ (inj₁ Bbb)) → ⟨ bb , Bbb ⟩
               ; (inj₂ (inj₂ Bcc)) → ⟨ cc , Bcc ⟩
               }
  ; from∘to = λ{ ⟨ aa , Baa ⟩ → refl
               ; ⟨ bb , Bbb ⟩ → refl
               ; ⟨ cc , Bcc ⟩ → refl
               }
  ; to∘from = λ{ (inj₁ Baa)        → refl
               ; (inj₂ (inj₁ Bbb)) → refl
               ; (inj₂ (inj₂ Bcc)) → refl
               }
  }

-- An existential example

data even : ℕ → Set
data odd  : ℕ → Set

data even where
  even-zero : even zero
  even-suc  : ∀ {n : ℕ}
    → odd n
      ------------
    → even (suc n)

data odd where
  odd-suc : ∀ {n : ℕ}
    → even n
      -----------
    → odd (suc n)

even-∃ : ∀ {n : ℕ} → even n → ∃[ m ] (    m * 2 ≡ n)
odd-∃  : ∀ {n : ℕ} →  odd n → ∃[ m ] (1 + m * 2 ≡ n)

even-∃ even-zero    = ⟨ zero , refl ⟩
even-∃ (even-suc o) with odd-∃ o
...                    | ⟨ m , refl ⟩ = ⟨ suc m , refl ⟩

odd-∃ (odd-suc e)   with even-∃ e
...                    | ⟨ m , refl ⟩ = ⟨ m , refl ⟩


∃-even : ∀ {n : ℕ} → ∃[ m ] (    m * 2 ≡ n) → even n
∃-odd  : ∀ {n : ℕ} → ∃[ m ] (1 + m * 2 ≡ n) → odd n

∃-even ⟨ zero , refl ⟩ = even-zero
∃-even ⟨ suc m , refl ⟩ = even-suc (∃-odd ⟨ m , refl ⟩ )

∃-odd ⟨ m , refl ⟩ = odd-suc (∃-even ⟨ m , refl ⟩ )

-- Exercise: ∃-even-odd

-- This is probably proved in the stdlib... but this works fine too.
m+1≡sm : ∀ (m : ℕ) → m + 1 ≡ suc m
m+1≡sm zero = refl
m+1≡sm (suc m) = cong suc (m+1≡sm m)

-- The actual exercise...

∃-even′ : ∀ {n : ℕ} → ∃[ m ] (    2 * m ≡ n) → even n
∃-odd′  : ∀ {n : ℕ} → ∃[ m ] (2 * m + 1 ≡ n) → odd n

∃-even′ ⟨ zero , refl ⟩ = even-zero
∃-even′ ⟨ suc m , refl ⟩ rewrite sym (m+1≡sm (m + zero))
                               | sym (+-assoc m (m + 0) 1)
                               = even-suc (∃-odd′ ⟨ m , refl ⟩)

∃-odd′ ⟨ zero , refl ⟩  = odd-suc even-zero
∃-odd′ ⟨ suc m , refl ⟩ rewrite m+1≡sm (m + suc (m + zero))
                               = odd-suc (∃-even′ ⟨ suc m , refl ⟩)
-- One day rewrite will not feel like trial & error with the compiler... one day.

-- Exercise: ∃-+-≤

y≤y : ∀ {y : ℕ} → y ≤ y
y≤y {zero} = z≤n
y≤y {suc y} = s≤s (y≤y {y})

∃+→≤ : ∀ {y z : ℕ} → ∃[ x ] (x + y ≡ z) → y ≤ z
∃+→≤ {y} ⟨ x , refl ⟩ =  +-mono-≤ {0} {x} {y} {y} z≤n y≤y

a∸b+b≡a : ∀ (a b : ℕ) → b ≤ a → a ∸ b + b ≡ a
a∸b+b≡a zero zero z≤n = refl
a∸b+b≡a (suc a) zero z≤n rewrite +-identityʳ a = refl
a∸b+b≡a (suc a) (suc b) (s≤s b≤a) rewrite +-comm (a ∸ b) (suc b) | +-comm b (a ∸ b) = cong suc (a∸b+b≡a a b b≤a)

≤→∃+ : ∀ {y z : ℕ} → y ≤ z → ∃[ x ] (x + y ≡ z)
≤→∃+ {y} {z} y≤z = ⟨ z ∸ y , a∸b+b≡a z y y≤z ⟩
