module Utils where

open import Level using (Level; 0ℓ; _⊔_) renaming (suc to ℓsuc) public
open import Data.Unit using (⊤; tt) public
open import Data.Empty using (⊥; ⊥-elim) public
open import Data.Bool using (Bool; true; false; not) public
open import Data.Nat using (ℕ; suc; zero) public
open import Data.Product using (Σ; ∃; _×_; _,_; proj₁; proj₂) public
open import Relation.Binary.PropositionalEquality 
  using (_≡_; refl; sym; subst; cong; cong-app; cong₂; dcong₂) public
  renaming (trans to infixr 4 _∙_) public
open import Relation.Binary.HeterogeneousEquality 
  using (_≅_; refl; ≅-to-≡; ≡-to-≅) 
  public

1ℓ = ℓsuc 0ℓ

even : ℕ → Bool
odd  : ℕ → Bool

even zero = true
even (suc m) = odd m

odd zero = false
odd (suc m) = even m

variable
  ℓ ℓ₁ ℓ₂ ℓ₃ : Level

coe : ∀ {A B : Set ℓ} → A ≡ B → A → B
coe = subst (λ x → x)

-- -- cong₂ : ∀ (f : A → B → C) {x y u v} → x ≡ y → u ≡ v → f x u ≡ f y v
-- -- cong₂ f refl refl = refl

-- cong-app : ∀ {A : Set a} {B : A → Set b} {f g : (x : A) → B x} {h →
--            f ≡ g → (x : A) → f x ≡ g x
-- cong-app refl x = refl
