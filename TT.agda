{-# OPTIONS --guardedness --rewriting #-}

import Agda.Builtin.Equality.Rewrite
open import Utils

-- An IIR fragment of a type theory syntax (thanks to Ambrus Kaposi for
-- suggesting this example)

-- WIP (there are some termination errors...)
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
    
    sem-wk : ∀ {ρ t} → into-set-ty A ρ → into-set-ty (wk {A = B} A) (ρ , t)
  
    -- We hit termination issues here. The main problematic calls appear to
    -- be these 'into-set-tm' cases and the 'El t' case of 'into-set-ty'
    {-# TERMINATING #-}
    into-set-tm (vz {A = A})   (ρ , t) = sem-wk {A = A} t
    into-set-tm (vs {A = A} t) (ρ , u) = sem-wk {A = A} (into-set-tm t ρ)

    -- We also need a mutual lemma about the semantics of 'wk'. This is
    -- probably a place where the flexibility to define our own interpretation
    -- of weakening before proving it satisfies the desired laws would be 
    -- useful.
    wk-ty : into-set-ty (wk {A = B} A) ≡ λ (ρ , _) → into-set-ty A ρ
    
    sem-wk {A = A} {ρ = ρ} {t = t} = coe (sym (cong-app (wk-ty {A = A}) (ρ , t)))

    wk-ty {A = U}     = refl
    wk-ty {A = El t}  = refl
    wk-ty {B = C} {A = A ⇒ B} 
      = cong₂ (λ A B → λ ρ → A ρ → B ρ) (wk-ty {A = A}) (wk-ty {A = B})

-- I first assumed the issue with termination here was due to Agda not knowing
-- 'wk A' sort-of preserves the size of the 'Ty'pe. Therefore, I also tried
-- recursing on 'Spine's

data Spine : Set where
  end : Spine
  _⇒_ : Spine → Spine → Spine

spine : Ty Γ → Spine
spine U       = end
spine (El _)  = end
spine (A ⇒ B) = spine A ⇒ spine B

spine-wk : spine (wk {A = B} A) ≡ spine A
spine-wk {A = U}     = refl
spine-wk {A = El t}  = refl
spine-wk {A = A ⇒ B} = cong₂ _⇒_ spine-wk spine-wk

{-# REWRITE spine-wk #-}

variable
  sA sB sC sD : Spine

module IntoSetSpines where
  into-set-con : Con → Set
  into-set-ty  : ∀ (A : Ty Γ) sA → sA ≡ spine A → into-set-con Γ → Set
  into-set-tm  : Tm Γ A → ∀ sA p → ∀ ρ → into-set-ty A sA p ρ 

  into-set-con •       = ⊤
  into-set-con (Γ ▷ A) = ∃ λ ρ → into-set-ty A (spine A) refl ρ

  into-set-ty U       end       refl ρ = Bool
  into-set-ty (El t)  end       refl ρ = large-elim (into-set-tm t end refl ρ)
  into-set-ty (A ⇒ B) (sA ⇒ sB) refl ρ 
    = into-set-ty A sA refl ρ → into-set-ty B sB refl ρ
  
  sem-wk : ∀ {ρ t} sA p → into-set-ty A sA p ρ 
          → into-set-ty (wk {A = B} A) sA p (ρ , t)

  -- Unfortunately, we hit essentially the same termination issues...
  {-# TERMINATING #-}
  into-set-tm (vz {A = A})   sA refl (ρ , t) 
    = sem-wk {A = A} sA refl t
  into-set-tm (vs {A = A} t) sA refl (ρ , u) 
    = sem-wk {A = A} sA refl (into-set-tm t sA refl ρ)

  wk-ty : ∀ sA p → into-set-ty (wk {A = B} A) sA p 
                  ≡ λ (ρ , _) → into-set-ty A sA p ρ
  
  sem-wk {A = A} {ρ = ρ} {t = t} sA p 
    = coe (sym (cong-app (wk-ty {A = A} sA p) (ρ , t)))

  wk-ty {A = U}             end       refl = refl
  wk-ty {A = El t}          end       refl = refl
  wk-ty {B = C} {A = A ⇒ B} (sA ⇒ sB) refl
    = cong₂ (λ A B → λ ρ → A ρ → B ρ) 
            (wk-ty {A = A} sA refl) (wk-ty {A = B} sB refl)

-- The reason I started with examples of pattern-matching on the syntax is that 
-- (spoilers) we will hit seemingly the exact same termination issues when
-- defining the general eliminator

-- Let's give it a shot anyway
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
    𝕞 : Methods
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

  -- Sure enough, we hit the same termination issues
  -- I also tried recursing on 'Spine's here and as to be expected, it doesn't
  -- really help here either (see 'TT-SpineElim.agda')
  {-# TERMINATING #-}
  elim-tm 𝕞 (vz {Γ = Γ} {A = A}) 
    = subst (λ m → Tmᴹ _ (elim-ty m (wk A)) vz) (𝕞-ext 𝕞) 
            (𝕞 .vzᴹ {Γᴱ = elim-con (𝕞 .self) Γ , refl} 
                    {Aᴱ = elim-ty (𝕞 .self) A , refl})
  elim-tm 𝕞 (vs {Γ = Γ} {A = A} {B = B} t) 
    = subst (λ m → Tmᴹ _ (elim-ty m (wk A)) (vs t)) (𝕞-ext 𝕞) 
            (𝕞 .vsᴹ {Γᴱ = elim-con (𝕞 .self) Γ , refl}
                    {Aᴱ = elim-ty (𝕞 .self) A , refl}
                    {Bᴱ = elim-ty (𝕞 .self) B , refl}
                    (elim-tm (𝕞 .self) t))

-- Small utility for interpreting into 'Set'
sem-wk : ∀ {Γᴹ : Set} {Bᴹ : Γᴹ → Set}
        → (Γᴹ → Set) → Σ Γᴹ (λ ρ → Bᴹ ρ) → Set
sem-wk Aᴹ (ρ , _) = Aᴹ ρ

-- After asserting termination, can we at least use the eliminator to interpret
-- into 'Set'?
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
    = coe (sym (cong-app (≅-to-≡ (wk-ty {B = A} {A = A})) (ρ , t))) t
  set-𝕞 .methods .vsᴹ {A = A} {B = B} {Γᴱ = _ , refl} {Aᴱ = _ , refl} 
                      tᴹ (ρ , u) 
    = coe (sym (cong-app (≅-to-≡ (wk-ty {B = B} {A = A})) (ρ , u))) (tᴹ ρ)

  wk-ty-𝕄 : Motive 0ℓ 1ℓ 0ℓ
  wk-ty-𝕄 .Conᴹ Γ     = ⊤
  wk-ty-𝕄 .Tyᴹ  Γᴹ A 
    = ∀ B → elim-ty set-𝕄 set-𝕞 (wk {A = B} A)
    ≡ sem-wk {Bᴹ = elim-ty set-𝕄 set-𝕞 B} (elim-ty set-𝕄 set-𝕞 A) 
  wk-ty-𝕄 .Tmᴹ Γᴹ Aᴹ t = ⊤

  wk-ty-𝕞 : Methods wk-ty-𝕄
  
  -- We need to assert termination when *using* the eliminator as well sadly...
  -- I think we might have a better shot with a single eliminator that
  -- simultaneously interprets into 'Set' and proves the 'wk-ty' lemma, but
  -- this seems quite tricky because the 'Motive' here would seemingly
  -- need to refer to elimination using itself
  {-# TERMINATING #-}
  wk-ty {B = B} {A = A} = ≡-to-≅ (elim-ty wk-ty-𝕄 wk-ty-𝕞 A B)
  
  wk-ty-𝕞 .methods .self = wk-ty-𝕞
  wk-ty-𝕞 .eq            = refl

  wk-ty-𝕞 .methods .•ᴹ       = tt
  wk-ty-𝕞 .methods ._▷ᴹ_ Γᴹ Aᴹ = tt

  wk-ty-𝕞 .methods .Uᴹ         B = refl
  wk-ty-𝕞 .methods .Elᴹ tᴹ     B = refl
  wk-ty-𝕞 .methods ._⇒ᴹ_ Aᴹ Bᴹ C 
    = cong₂ (λ A B → λ ρ → A ρ → B ρ) (Aᴹ C) (Bᴹ C)

  wk-ty-𝕞 .methods .vzᴹ    = tt
  wk-ty-𝕞 .methods .vsᴹ tᴹ = tt
