module plfa.part1.Quantifiers where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
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
