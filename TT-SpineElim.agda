{-# OPTIONS --guardedness --rewriting #-}

open import Utils
open import TT

module TT-SpineElim {ℓ₁ ℓ₂ ℓ₃} (𝕄 : Motive ℓ₁ ℓ₂ ℓ₃) where

open Motive 𝕄

variable
  Γᴹ Δᴹ Θᴹ Ξᴹ : Conᴹ Γ
  Aᴹ Bᴹ Cᴹ Dᴹ : Tyᴹ Γᴹ A
  tᴹ uᴹ vᴹ    : Tmᴹ Γᴹ Aᴹ t

record Methods : Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃)

elim-con : Methods → ∀ Γ → Conᴹ Γ
elim-ty  : ∀ 𝕞 A sA → sA ≡ spine A → Tyᴹ (elim-con 𝕞 Γ) A
elim-tm  : ∀ 𝕞 t sA p → Tmᴹ (elim-con 𝕞 Γ) (elim-ty 𝕞 A sA p) t

record Conᴱ (𝕞 : Methods) (Γ : Con) : Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃) where
  constructor _,_
  field
    Con-out : Conᴹ Γ
    Con-eq  : elim-con 𝕞 Γ ≡ Con-out
open Conᴱ

record Tyᴱ (𝕞 : Methods) (Γᴱ : Conᴱ 𝕞 Γ) (A : Ty Γ) : Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃) where
  constructor _,_
  field
    Ty-out : Tyᴹ (Γᴱ .Con-out) A
    Ty-eq  : elim-ty 𝕞 A (spine A) refl 
            ≡ subst (λ Γᴹ → Tyᴹ Γᴹ A) (sym (Γᴱ .Con-eq)) Ty-out
open Tyᴱ

variable
  𝕞 : Methods
  Γᴱ Δᴱ Θᴱ Ξᴱ : Conᴱ 𝕞 Γ
  Aᴱ Bᴱ Cᴱ Dᴱ : Tyᴱ 𝕞 Γᴱ A

-- These 'ᴱ' methods being so trivial makes me feel like I might be 
-- overcomplicating this a bit...
_▷ᴱ_ : ∀ Γᴱ → Tyᴱ 𝕞 Γᴱ A → Conᴱ 𝕞 (Γ ▷ A)
_▷ᴱ_ {𝕞 = 𝕞} {Γ = Γ} {A = A} _ _ = elim-con 𝕞 (Γ ▷ A) , refl

wkᴱ : Tyᴱ 𝕞 Γᴱ B → Tyᴱ 𝕞 (Γᴱ ▷ᴱ Aᴱ) (wk B)
wkᴱ {𝕞 = 𝕞} {B = B} _ = elim-ty 𝕞 (wk B) (spine B) refl , refl

record PreMethods : Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃) where
  coinductive
  field
    self : Methods

    •ᴹ   : Conᴹ •
    _▷ᴹ_ : ∀ Γᴹ → Tyᴹ Γᴹ A → Conᴹ (Γ ▷ A)

    Uᴹ   : Tyᴹ Γᴹ U
    Elᴹ  : Tmᴹ Γᴹ Uᴹ t → Tyᴹ Γᴹ (El t)
    _⇒ᴹ_ : Tyᴹ Γᴹ A → Tyᴹ Γᴹ B → Tyᴹ Γᴹ (A ⇒ B)

    -- Note it is critical we don't generalise over '𝕞' here. It needs to be
    -- 'self' to have everything match up
    vzᴹ  : ∀ {Γᴱ : Conᴱ self Γ} {Aᴱ : Tyᴱ self Γᴱ A} 
          → Tmᴹ ((Γᴱ ▷ᴱ Aᴱ) .Con-out) (wkᴱ {Aᴱ = Aᴱ} Aᴱ .Ty-out) vz
    vsᴹ  : ∀ {Γᴱ : Conᴱ self Γ} {Aᴱ : Tyᴱ self Γᴱ A} {Bᴱ : Tyᴱ self Γᴱ B}
          → Tmᴹ (Γᴱ .Con-out) (Aᴱ .Ty-out) t
          → Tmᴹ ((Γᴱ ▷ᴱ Bᴱ) .Con-out) (wkᴱ {Aᴱ = Bᴱ} Aᴱ .Ty-out) (vs t)

methods-fwd : Methods → PreMethods
record Methods where
  constructor _,m_
  inductive
  eta-equality
  field
    methods : PreMethods
    eq      : methods-fwd (methods .PreMethods.self) ≡ methods
  open PreMethods methods public
open Methods
methods-fwd = methods

uip : ∀ {a} {A : Set a} {x y : A} {p q : x ≡ y} → p ≡ q
uip {p = refl} {q = refl} = refl

𝕞-ext : ∀ 𝕞 → 𝕞 .self ≡ 𝕞
𝕞-ext (𝕞 ,m p) = dcong₂ _,m_ p uip

elim-con 𝕞 •       = 𝕞 .•ᴹ
elim-con 𝕞 (Γ ▷ A) = 𝕞 ._▷ᴹ_ (elim-con 𝕞 Γ) (elim-ty 𝕞 A (spine A) refl)

elim-ty 𝕞 U       end refl       = 𝕞 .Uᴹ
elim-ty 𝕞 (El t)  end refl       = 𝕞 .Elᴹ (elim-tm 𝕞 t end refl)
elim-ty 𝕞 (A ⇒ B) (sA ⇒ sB) refl 
  = 𝕞 ._⇒ᴹ_ (elim-ty 𝕞 A sA refl) (elim-ty 𝕞 B sB refl)

-- Sure enough, we need to assert termination here also
{-# TERMINATING #-}
elim-tm 𝕞 (vz {Γ = Γ} {A = A}) sA refl
  = subst (λ m → Tmᴹ _ (elim-ty m (wk A) sA refl) vz) (𝕞-ext 𝕞) 
          (𝕞 .vzᴹ {Γᴱ = elim-con (𝕞 .self) Γ , refl} 
                  {Aᴱ = elim-ty (𝕞 .self) A sA refl , refl})
elim-tm 𝕞 (vs {Γ = Γ} {A = A} {B = B} t) sA refl
  = subst (λ m → Tmᴹ _ (elim-ty m (wk A) sA refl) (vs t)) (𝕞-ext 𝕞) 
          (𝕞 .vsᴹ {Γᴱ = elim-con (𝕞 .self) Γ , refl}
                  {Aᴱ = elim-ty (𝕞 .self) A sA refl , refl}
                  {Bᴱ = elim-ty (𝕞 .self) B (spine B) refl , refl}
                  (elim-tm (𝕞 .self) t sA refl))