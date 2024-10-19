module Utils where

open import Level using (Level; 0ℓ; _⊔_) renaming (suc to ℓsuc) public
open import Data.Unit using (⊤; tt) public
open import Data.Empty using (⊥; ⊥-elim) public
open import Data.Bool using (Bool; true; false; not) public
open import Data.Nat using (ℕ; suc; zero) public
open import Relation.Binary.PropositionalEquality 
  using (_≡_; refl; subst; cong; sym; dcong₂) public
  renaming (trans to infixr 4 _∙_) public

1ℓ = ℓsuc 0ℓ

even : ℕ → Bool
odd  : ℕ → Bool

even zero = true
even (suc m) = odd m

odd zero = false
odd (suc m) = even m

variable
  ℓ ℓ₁ ℓ₂ : Level
