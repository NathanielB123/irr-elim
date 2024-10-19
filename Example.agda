{-# OPTIONS --guardedness #-}

open import Utils 

module Example where

module SimpleIndRec where
  data U : Set
  El : U → Set

  data U where
    𝔹 : U
    Π : ∀ A → (El A → U) → U

  El 𝔹       = Bool
  El (Π A B) = ∀ a → El (B a)

  variable
    A : U
    B : El A → U

  record Motive : Set₁ where
    field
      Uᴹ : U → Set

  record Methods (𝕄 : Motive) : Set where
    open Motive 𝕄
    
    field
      𝔹ᴹ : Uᴹ 𝔹
      Πᴹ : Uᴹ A → ((a : El A) → Uᴹ (B a)) → Uᴹ (Π A B)

data A : Set
data B : A → Set
foo : A → A

variable
  a a₁ a₂ : A
  b b₁ b₂ : B a

data A where
  U₁ U₂ : A
  El : B U₁ → A

data B where
  Z : B U₁
  ap : B a → B (foo a)

foo U₁     = U₂
foo U₂     = U₁
foo (El b) = El b

record Motive ℓ₁ ℓ₂ : Set (ℓsuc (ℓ₁ ⊔ ℓ₂)) where
  field
    Aᴹ : A → Set ℓ₁
    Bᴹ : Aᴹ a → B a → Set ℓ₂

module MethodsMod {ℓ₁} {ℓ₂} (𝕄 : Motive ℓ₁ ℓ₂) where 
  open Motive 𝕄

  variable
    aᴹ a₁ᴹ a₂ᴹ : Aᴹ a
    bᴹ b₁ᴹ b₂ᴹ : Bᴹ aᴹ b

  record Methods : Set (ℓ₁ ⊔ ℓ₂)
  
  elim-A : Methods → ∀ a → Aᴹ a
  elim-B : (𝕞 : Methods) → ∀ b → Bᴹ (elim-A 𝕞 a) b

  -- 'Aᴹ' restricted to the range of the eliminator
  record Aᴱ (𝕞 : Methods) (a : A) : Set (ℓ₁ ⊔ ℓ₂) where
    constructor _,_
    inductive
    eta-equality
    field
      A-out : Aᴹ a
      A-coh : elim-A 𝕞 a ≡ A-out
  open Aᴱ public

  -- What we want to avoid adding a case for...
  fooᴱ : ∀ 𝕞 → Aᴱ 𝕞 a → Aᴱ 𝕞 (foo a)

  record PreMethods : Set (ℓ₁ ⊔ ℓ₂) where
    coinductive
    field
      self : Methods

      U₁ᴹ : Aᴹ U₁
      U₂ᴹ : Aᴹ U₂
      Elᴹ : Bᴹ U₁ᴹ b → Aᴹ (El b)
      Zᴹ  : Bᴹ U₁ᴹ Z
      apᴹ : ∀ {aᴱ : Aᴱ self a} 
          → Bᴹ (aᴱ .A-out) b → Bᴹ (fooᴱ self aᴱ .A-out) (ap b)

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
  methods-fwd 𝕞 = 𝕞 .methods

  fooᴱ {a = a} 𝕞 (aᴹ , p) = elim-A 𝕞 (foo a) , refl

  -- TODO: Can we craft a version that doesn't require UIP?
  uip : ∀ {a} {A : Set a} {x y : A} {p q : x ≡ y} → p ≡ q
  uip {p = refl} {q = refl} = refl

  𝕞-ext : ∀ {𝕞 : Methods} → 𝕞 .self ≡ 𝕞
  𝕞-ext {𝕞 = 𝕞 ,m p} = dcong₂ _,m_ p uip

  elim-A 𝕞 U₁ = 𝕞 .U₁ᴹ
  elim-A 𝕞 U₂ = 𝕞 .U₂ᴹ
  elim-A 𝕞 (El b) = 𝕞 .Elᴹ (elim-B 𝕞 b)

  elim-B 𝕞 Z      = 𝕞 .Zᴹ
  -- I inline 'foo' here to ensure termination
  -- elim-B 𝕞 (ap {a = a} b) 
  --   = subst (λ m → Bᴹ (elim-A m (foo a)) _) 𝕞-ext
  --           (𝕞 .apᴹ {aᴱ = aᴱ} (elim-B (𝕞 .self) b))
  --    where aᴱ = elim-A (𝕞 .self) a , refl
  elim-B 𝕞 (ap {a = a@U₁} b) 
    = subst (λ m → Bᴹ (elim-A m U₂) (ap b)) (𝕞-ext {𝕞 = 𝕞})
            (𝕞 .apᴹ {aᴱ = aᴱ} (elim-B (𝕞 .self) b))
      where aᴱ = elim-A (𝕞 .self) a , refl
  elim-B 𝕞 (ap {a = a@U₂} b) 
    = subst (λ m → Bᴹ (elim-A m U₁) (ap b)) (𝕞-ext {𝕞 = 𝕞})
            (𝕞 .apᴹ {aᴱ = aᴱ} (elim-B (𝕞 .self) b))
      where aᴱ = elim-A (𝕞 .self) a , refl
  elim-B 𝕞 (ap {a = a@(El _)} b) 
    = subst (λ m → Bᴹ (elim-A m a) (ap b)) (𝕞-ext {𝕞 = 𝕞})
            (𝕞 .apᴹ {aᴱ = elim-A (𝕞 .self) a , refl} (elim-B (𝕞 .self) b))

open MethodsMod public
open Motive public
open Methods using (methods; eq) public
open PreMethods public

trivial-𝕄 : Motive 0ℓ 0ℓ
trivial-𝕄 .Aᴹ _ = ⊤
trivial-𝕄 .Bᴹ _ _ = ⊤

trivial-𝕞 : Methods trivial-𝕄
trivial-𝕞 .methods .self   = trivial-𝕞
trivial-𝕞 .eq              = refl
trivial-𝕞 .methods .U₁ᴹ    = tt
trivial-𝕞 .methods .U₂ᴹ    = tt
trivial-𝕞 .methods .Elᴹ bᴹ = tt
trivial-𝕞 .methods .Zᴹ     = tt
trivial-𝕞 .methods .apᴹ bᴹ = tt

test : elim-B trivial-𝕄 trivial-𝕞 Z ≡ tt
test = refl

set-𝕄 : Motive 1ℓ 0ℓ
set-𝕄 .Aᴹ _ = Set
set-𝕄 .Bᴹ Aᴹ _ = Aᴹ

set-𝕞 : Methods set-𝕄
set-𝕞 .methods .self  = set-𝕞
set-𝕞 .eq             = refl
set-𝕞 .methods .U₁ᴹ   = Bool
set-𝕞 .methods .U₂ᴹ   = ℕ
set-𝕞 .methods .Elᴹ _ = ⊤
set-𝕞 .methods .Zᴹ = false
set-𝕞 .methods .apᴹ {a = U₁}   {aᴱ = aᴹ , refl} false = 1
set-𝕞 .methods .apᴹ {a = U₁}   {aᴱ = aᴹ , refl} true  = 0
set-𝕞 .methods .apᴹ {a = U₂}   {aᴱ = aᴹ , refl} bᴹ    = even bᴹ
set-𝕞 .methods .apᴹ {a = El b} {aᴱ = aᴹ , refl} bᴹ    = tt
  
test-2 : elim-B set-𝕄 set-𝕞 (ap (ap Z)) ≡ false
test-2 = refl