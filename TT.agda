{-# OPTIONS --guardedness --rewriting #-}

import Agda.Builtin.Equality.Rewrite
open import Utils

-- An IIR fragment of a type theory syntax (thanks to Ambrus Kaposi for
-- suggesting this example)

-- WIP (I have asserted termination when using the eliminator)
module TT where

data Con : Set
data Ty  : Con → Set
data Tm  : (Γ : Con) → Ty Γ → Set

variable
  Γ Δ Θ Ξ : Con
  A B C D : Ty Γ
  t u v   : Tm Γ A

data Con where
  •   : Con
  _▷_ : ∀ Γ → Ty Γ → Con

data Ty where
  U   : Ty Γ
  El  : Tm Γ U → Ty Γ
  _⇒_ : Ty Γ → Ty Γ → Ty Γ

wk : Ty Γ → Ty (Γ ▷ A)

data Tm where
  vz : Tm (Γ ▷ A) (wk A)
  vs : Tm Γ A → Tm (Γ ▷ B) (wk A)

wk U       = U
wk (El a)  = El (vs a)
wk (A ⇒ B) = wk A ⇒ wk B

large-elim : Bool → Set
large-elim true  = ⊤
large-elim false = ⊥

-- First we try to eliminate into 'Set' with pattern matching
-- This was a bit trickier than I expected...

module IntoSetPatternMatching where
    into-set-con : Con → Set
    into-set-ty  : Ty Γ → into-set-con Γ → Set
    into-set-tm  : Tm Γ A → ∀ ρ → into-set-ty A ρ

    into-set-con •       = ⊤
    into-set-con (Γ ▷ A) = ∃ λ ρ → into-set-ty A ρ

    into-set-ty U       ρ = Bool
    into-set-ty (El t)  ρ = large-elim (into-set-tm t ρ)
    into-set-ty (A ⇒ B) ρ = into-set-ty A ρ → into-set-ty B ρ
    
    wk-coe : ∀ {ρ t} → into-set-ty A ρ → into-set-ty (wk {A = B} A) (ρ , t)
  
    into-set-tm (vz {A = A})   (ρ , t) = wk-coe {A = A} t
    into-set-tm (vs {A = A} t) (ρ , u) = wk-coe {A = A} (into-set-tm t ρ)

    wk-ty : into-set-ty (wk {A = B} A) ≡ λ (ρ , _) → into-set-ty A ρ
    
    -- Thanks to Szumi Xie for suggesting writing specific helpers for
    -- 'wk-coe'/'wk-ty' instead of generic 'coe'/'cong-app'/'cong₂', to avoid
    -- termination errors
    wk-coe-helper : ∀ {X ρ} → into-set-ty (wk {A = B} A) ≡ X
                  → X ρ → into-set-ty (wk {A = B} A) ρ

    wk-coe {A = A} {ρ = ρ} {t = t} = wk-coe-helper {A = A} (wk-ty {A = A})

    wk-coe-helper refl x = x

    wk-ty-⇒-helper : ∀ {X Y} →
      into-set-ty (wk {A = C} A) ≡ X →
      into-set-ty (wk {A = C} B) ≡ Y →
      (λ ρ → into-set-ty (wk {A = C} A) ρ → into-set-ty (wk {A = C} B) ρ) ≡
      (λ ρ → X ρ → Y ρ)
    wk-ty-⇒-helper refl refl = refl

    wk-ty {A = U}     = refl
    wk-ty {A = El t}  = refl
    wk-ty {B = C} {A = A ⇒ B} 
      = wk-ty-⇒-helper {A = A} {B = B} (wk-ty {A = A}) (wk-ty {A = B})


record Motive (ℓ₁ ℓ₂ ℓ₃ : Level) : Set (ℓsuc (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃)) where
  field
    Conᴹ : Con → Set ℓ₁
    Tyᴹ  : Conᴹ Γ → Ty Γ → Set ℓ₂
    Tmᴹ  : ∀ Γᴹ → Tyᴹ Γᴹ A → Tm Γ A → Set ℓ₃

module Elim {ℓ₁ ℓ₂ ℓ₃} (𝕄 : Motive ℓ₁ ℓ₂ ℓ₃) where
  open Motive 𝕄

  variable
    Γᴹ Δᴹ Θᴹ Ξᴹ : Conᴹ Γ
    Aᴹ Bᴹ Cᴹ Dᴹ : Tyᴹ Γᴹ A
    tᴹ uᴹ vᴹ    : Tmᴹ Γᴹ Aᴹ t
  
  record Methods : Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃)

  elim-con : Methods → ∀ Γ → Conᴹ Γ
  elim-ty  : ∀ 𝕞 A → Tyᴹ (elim-con 𝕞 Γ) A
  elim-tm  : ∀ 𝕞 t → Tmᴹ (elim-con 𝕞 Γ) (elim-ty 𝕞 A) t

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
      Ty-eq  : elim-ty 𝕞 A ≡ subst (λ Γᴹ → Tyᴹ Γᴹ A) (sym (Γᴱ .Con-eq)) Ty-out
  open Tyᴱ

  variable
    𝕞 𝕞₁ 𝕞₂ : Methods
    Γᴱ Δᴱ Θᴱ Ξᴱ : Conᴱ 𝕞 Γ
    Aᴱ Bᴱ Cᴱ Dᴱ : Tyᴱ 𝕞 Γᴱ A

  -- These 'ᴱ' methods being so trivial makes me feel like I might be 
  -- overcomplicating this a bit...
  _▷ᴱ_ : ∀ Γᴱ → Tyᴱ 𝕞 Γᴱ A → Conᴱ 𝕞 (Γ ▷ A)
  _▷ᴱ_ {𝕞 = 𝕞} {Γ = Γ} {A = A} _ _ = elim-con 𝕞 (Γ ▷ A) , refl
  
  wkᴱ : Tyᴱ 𝕞 Γᴱ B → Tyᴱ 𝕞 (Γᴱ ▷ᴱ Aᴱ) (wk B)
  wkᴱ {𝕞 = 𝕞} {B = B} _ = elim-ty 𝕞 (wk B) , refl

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
  elim-con 𝕞 (Γ ▷ A) = 𝕞 ._▷ᴹ_ (elim-con 𝕞 Γ) (elim-ty 𝕞 A)
  
  elim-ty 𝕞 U       = 𝕞 .Uᴹ
  elim-ty 𝕞 (El t)  = 𝕞 .Elᴹ (elim-tm 𝕞 t)
  elim-ty 𝕞 (A ⇒ B) = 𝕞 ._⇒ᴹ_ (elim-ty 𝕞 A) (elim-ty 𝕞 B)

  coe-methods-tm : 𝕞₁ ≡ 𝕞₂ 
                 → Tmᴹ (elim-con 𝕞₁ Γ) (elim-ty 𝕞₁ A) t 
                 → Tmᴹ (elim-con 𝕞₂ Γ) (elim-ty 𝕞₂ A) t
  coe-methods-tm refl x = x

  elim-tm 𝕞 (vz {Γ = Γ} {A = A}) 
    = coe-methods-tm (𝕞-ext 𝕞) (𝕞 .vzᴹ {Γᴱ = elim-con (𝕞 .self) Γ , refl} 
                                       {Aᴱ = elim-ty  (𝕞 .self) A , refl})
  elim-tm 𝕞 (vs {Γ = Γ} {A = A} {B = B} t) 
    = coe-methods-tm (𝕞-ext 𝕞) (𝕞 .vsᴹ {Γᴱ = elim-con (𝕞 .self) Γ , refl}
                                       {Aᴱ = elim-ty  (𝕞 .self) A , refl}
                                       {Bᴱ = elim-ty  (𝕞 .self) B , refl}
                                       (elim-tm (𝕞 .self) t))

-- Desired behaviour for 'elim-ty ... (wk A)'
sem-wk : ∀ {Γᴹ : Set} {Bᴹ : Γᴹ → Set}
        → (Γᴹ → Set) → Σ Γᴹ (λ ρ → Bᴹ ρ) → Set
sem-wk Aᴹ (ρ , _) = Aᴹ ρ


module WithElim where
  open Elim
  open Motive
  open Methods
  open PreMethods

  set-𝕄 : Motive 1ℓ 1ℓ 0ℓ
  set-𝕞 : Methods set-𝕄

  set-𝕄 .Conᴹ Γ       = Set
  set-𝕄 .Tyᴹ  Γᴹ A    = Γᴹ → Set
  set-𝕄 .Tmᴹ  Γᴹ Aᴹ t = ∀ ρ → Aᴹ ρ

  wk-ty : elim-ty set-𝕄 set-𝕞 (wk {A = B} A)
        ≅ sem-wk {Bᴹ = elim-ty set-𝕄 set-𝕞 B} (elim-ty set-𝕄 set-𝕞 A) 
  
  wk-coe-helper : ∀ {X ρ} 
                → elim-ty set-𝕄 set-𝕞 (wk {A = B} A) ≡ X
                → X ρ → elim-ty set-𝕄 set-𝕞 (wk {A = B} A) ρ
  wk-coe-helper refl x = x

  -- Version of 'wk-coe-helper' that takes a '≅' just in case that assists 
  -- with termination
  wk-coe-helper≅ : ∀ {B : Ty Γ} 
                     {X : set-𝕞 .methods ._▷ᴹ_ (elim-con set-𝕄 set-𝕞 Γ) 
                                               (elim-ty  set-𝕄 set-𝕞 B) → Set}
                     {ρ} 
                → elim-ty set-𝕄 set-𝕞 (wk {A = B} A) ≅ X
                → X ρ → elim-ty set-𝕄 set-𝕞 (wk {A = B} A) ρ
  wk-coe-helper≅ refl x = x

  -- I don't know how to avoid asserting termination here. Unfortunately,
  -- Szumi's trick of writing a concrete coerce function doesn't appear to be
  -- enough
  {-# TERMINATING #-}
  set-𝕞 .methods .self = set-𝕞 
  set-𝕞 .eq            = refl
  
  set-𝕞 .methods .•ᴹ         = ⊤
  set-𝕞 .methods ._▷ᴹ_ Γᴹ Aᴹ = ∃ λ ρ → Aᴹ ρ

  set-𝕞 .methods .Uᴹ  
    = λ _ → Bool       
  set-𝕞 .methods .Elᴹ tᴹ
    = λ ρ → large-elim (tᴹ ρ)
  set-𝕞 .methods ._⇒ᴹ_ Aᴹ Bᴹ 
    = λ ρ → Aᴹ ρ → Bᴹ ρ
  
  set-𝕞 .methods .vzᴹ {A = A} (ρ , t) 
    = wk-coe-helper {A = A} (≅-to-≡ (wk-ty {B = A} {A = A})) t
    -- = coe (sym (cong-app (≅-to-≡ (wk-ty {B = A} {A = A})) (ρ , t))) t
  set-𝕞 .methods .vsᴹ {A = A} {B = B} {Γᴱ = _ , refl} {Aᴱ = _ , refl} 
                      tᴹ (ρ , u) 
    = wk-coe-helper {A = A} (≅-to-≡ (wk-ty {B = B} {A = A})) (tᴹ ρ)
    -- = coe (sym (cong-app (≅-to-≡ (wk-ty {B = B} {A = A})) (ρ , u))) (tᴹ ρ)

  wk-ty-𝕄 : Motive 0ℓ 1ℓ 0ℓ
  wk-ty-𝕄 .Conᴹ Γ     = ⊤
  wk-ty-𝕄 .Tyᴹ  Γᴹ A 
    = ∀ B → elim-ty set-𝕄 set-𝕞 (wk {A = B} A)
    ≡ sem-wk {Bᴹ = elim-ty set-𝕄 set-𝕞 B} (elim-ty set-𝕄 set-𝕞 A) 
  wk-ty-𝕄 .Tmᴹ Γᴹ Aᴹ t = ⊤

  wk-ty-𝕞 : Methods wk-ty-𝕄
  
  wk-ty {B = B} {A = A} = ≡-to-≅ (elim-ty wk-ty-𝕄 wk-ty-𝕞 A B)
  
  wk-ty-𝕞 .methods .self = wk-ty-𝕞
  wk-ty-𝕞 .eq            = refl

  wk-ty-𝕞 .methods .•ᴹ         = tt
  wk-ty-𝕞 .methods ._▷ᴹ_ Γᴹ Aᴹ = tt

  wk-ty-𝕞 .methods .Uᴹ         B = refl
  wk-ty-𝕞 .methods .Elᴹ tᴹ     B = refl
  wk-ty-𝕞 .methods ._⇒ᴹ_ Aᴹ Bᴹ C 
    = cong₂ (λ A B → λ ρ → A ρ → B ρ) (Aᴹ C) (Bᴹ C)

  wk-ty-𝕞 .methods .vzᴹ    = tt
  wk-ty-𝕞 .methods .vsᴹ tᴹ = tt

  test : elim-tm set-𝕄 set-𝕞 (vs  {Γ = ((• ▷ U) ▷ U) ▷ U} {B = U} (vs vz)) 
       ≡ (λ (((_ , t) , _) , _) → t)
  test = refl


module StandardElim {ℓ₁ ℓ₂ ℓ₃} (𝕄 : Motive ℓ₁ ℓ₂ ℓ₃) where
  open Motive 𝕄

  variable
    Γᴹ Δᴹ Θᴹ Ξᴹ : Conᴹ Γ
    Aᴹ Bᴹ Cᴹ Dᴹ : Tyᴹ Γᴹ A
    tᴹ uᴹ vᴹ    : Tmᴹ Γᴹ Aᴹ t
  
  record Methods : Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃) where
    field
      •ᴹ   : Conᴹ •
      _▷ᴹ_ : ∀ Γᴹ → Tyᴹ Γᴹ A → Conᴹ (Γ ▷ A)

      Uᴹ   : Tyᴹ Γᴹ U
      Elᴹ  : Tmᴹ Γᴹ Uᴹ t → Tyᴹ Γᴹ (El t)
      _⇒ᴹ_ : Tyᴹ Γᴹ A → Tyᴹ Γᴹ B → Tyᴹ Γᴹ (A ⇒ B)

      wkᴹ  : Tyᴹ Γᴹ A → Tyᴹ (Γᴹ ▷ᴹ Bᴹ) (wk A)

      vzᴹ  : Tmᴹ (Γᴹ ▷ᴹ Aᴹ) (wkᴹ {Bᴹ = Aᴹ} Aᴹ) vz
      vsᴹ  : Tmᴹ Γᴹ Aᴹ t  → Tmᴹ (Γᴹ ▷ᴹ Bᴹ) (wkᴹ {Bᴹ = Bᴹ} Aᴹ) (vs t)

      wkUᴹ  : wkᴹ {Bᴹ = Bᴹ} Uᴹ ≡ Uᴹ
      wkElᴹ : wkᴹ {Bᴹ = Bᴹ} (Elᴹ tᴹ)
            ≡ Elᴹ (subst (λ Aᴹ → Tmᴹ _ Aᴹ (vs t)) wkUᴹ (vsᴹ tᴹ))
      wk⇒ᴹ  : wkᴹ {Bᴹ = Cᴹ} (Aᴹ ⇒ᴹ Bᴹ) ≡ wkᴹ Aᴹ ⇒ᴹ wkᴹ Bᴹ

  module ElimMethods (𝕞 : Methods) where
    open Methods 𝕞

    elim-con : ∀ Γ → Conᴹ Γ
    elim-ty  : ∀ A → Tyᴹ  (elim-con Γ) A
    elim-tm  : ∀ t → Tmᴹ  (elim-con Γ) (elim-ty A) t

    elim-con •       = •ᴹ
    elim-con (Γ ▷ A) = elim-con Γ ▷ᴹ elim-ty A
    
    elim-ty U       = Uᴹ
    elim-ty (El t)  = Elᴹ (elim-tm t)
    elim-ty (A ⇒ B) = elim-ty A ⇒ᴹ elim-ty B

    coe-wk-tm : ∀ {wkAᴹ} → wkAᴹ ≡ elim-ty (wk A)
              → Tmᴹ (elim-con Γ ▷ᴹ elim-ty B) wkAᴹ t
              → Tmᴹ (elim-con Γ ▷ᴹ elim-ty B) (elim-ty (wk A)) t
    coe-wk-tm refl tᴹ = tᴹ

    wk-ty : wkᴹ (elim-ty A) ≡ elim-ty (wk {A = B} A)

    elim-tm vz     = coe-wk-tm wk-ty vzᴹ
    elim-tm (vs t) = coe-wk-tm wk-ty (vsᴹ (elim-tm t))

    wk-El : ∀ {wkElᴹ coe-fn p}
          → wkElᴹ  ≡ Elᴹ (subst (λ Aᴹ → Tmᴹ _ Aᴹ t) p tᴹ)
          → coe-fn ≡ subst (λ Aᴹ → Tmᴹ _ Aᴹ t) p
          → wkElᴹ  ≡ Elᴹ (coe-fn tᴹ)
    wk-El refl refl = refl

    wk-⇒ : ∀ {wkAᴹ wkBᴹ wkABᴹ} → wkABᴹ ≡ wkAᴹ ⇒ᴹ wkBᴹ 
         → wkAᴹ ≡ elim-ty (wk {A = C} A) → wkBᴹ ≡ elim-ty (wk B)
         → wkABᴹ ≡ elim-ty (wk A) ⇒ᴹ elim-ty (wk B)
    wk-⇒ refl refl refl = refl

    coe-wk-tm-subst : ∀ {wkAᴹ} (p : wkAᴹ ≡ elim-ty (wk {Γ = Γ} A)) 
                    → coe-wk-tm p ≡ subst (λ Aᴹ → Tmᴹ _ Aᴹ (vs {B = B} t)) p
    coe-wk-tm-subst refl = refl

    wk-ty {A = U}     = wkUᴹ
    wk-ty {A = El t}  = wk-El wkElᴹ (coe-wk-tm-subst wkUᴹ)
    wk-ty {A = A ⇒ B} = wk-⇒ wk⇒ᴹ (wk-ty {A = A}) (wk-ty {A = B})
  open ElimMethods public

-- It turns out that with the standard 'wkᴹ' eliminator, interpreting into 'Set'
-- comes out beautifully, with no need for coercions or extra lemmas.
-- I think this very much puts in doubt the motivation for the leaner 'Methods'
-- record - 'wkᴹ' as a case does provide useful flexibility
module WithStandardElim where
  open StandardElim
  open Motive
  open Methods
  
  set-𝕄 : Motive 1ℓ 1ℓ 0ℓ
  set-𝕄 .Conᴹ Γ       = Set
  set-𝕄 .Tyᴹ  Γᴹ A    = Γᴹ → Set
  set-𝕄 .Tmᴹ  Γᴹ Aᴹ t = ∀ ρ → Aᴹ ρ

  set-𝕞 : Methods set-𝕄
  set-𝕞 .•ᴹ         = ⊤
  set-𝕞 ._▷ᴹ_ Γᴹ Aᴹ = ∃ λ ρ → Aᴹ ρ

  set-𝕞 .Uᴹ   _       = Bool
  set-𝕞 .Elᴹ  tᴹ ρ    = large-elim (tᴹ ρ)
  set-𝕞 ._⇒ᴹ_ Aᴹ Bᴹ ρ = Aᴹ ρ → Bᴹ ρ
  
  set-𝕞 .wkᴹ Aᴹ (ρ , _) = Aᴹ ρ

  set-𝕞 .vzᴹ    (ρ , t) = t
  set-𝕞 .vsᴹ tᴹ (ρ , _) = tᴹ ρ

  set-𝕞 .wkUᴹ  = refl
  set-𝕞 .wkElᴹ = refl
  set-𝕞 .wk⇒ᴹ  = refl
