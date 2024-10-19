{-# OPTIONS --guardedness #-}

open import Utils 

module Example where

-- This is our inductive-inductive-recursive type we want to eliminate. 
-- It isn't really meant to model anything meaningful. Just complicated enough 
-- to have a non-trivial recursive function.
--
-- I would be very interested to hear about some small but still useful 
-- IIR-types. The main case I am interested is the syntax of a dependent type
-- theory, but this makes for a much more complicated example...
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

-- The 'Motive' is easy...
record Motive ℓ₁ ℓ₂ : Set (ℓsuc (ℓ₁ ⊔ ℓ₂)) where
  field
    Aᴹ : A → Set ℓ₁
    Bᴹ : Aᴹ a → B a → Set ℓ₂

-- The 'Methods' (i.e. proofs of the 'Motive' for each constructor) are 
-- trickier. Specifically, the 'ap' case seemingly requires us to have a
-- version of 'foo' lifted to 'Aᴹ'. The approach taken in 
-- https://akaposi.github.io/pres_types_2023.pdf
-- is to add a case for this non-canonical element + equations, so let's try
-- that first.

module BadElim {ℓ₁} {ℓ₂} (𝕄 : Motive ℓ₁ ℓ₂) where
  open Motive 𝕄
  
  variable
    aᴹ a₁ᴹ a₂ᴹ : Aᴹ a
    bᴹ b₁ᴹ b₂ᴹ : Bᴹ aᴹ b
  
  record Methods : Set (ℓ₁ ⊔ ℓ₂) where
    field
      U₁ᴹ : Aᴹ U₁
      U₂ᴹ : Aᴹ U₂
      Elᴹ : Bᴹ U₁ᴹ b → Aᴹ (El b)

      -- Case for non-canonical 'foo a' elements:
      fooᴹ   : Aᴹ a → Aᴹ (foo a)
      -- Plus equations...
      -- At least we don't need to coerce...
      fooU₁ᴹ : fooᴹ U₁ᴹ      ≡ U₂ᴹ
      fooU₂ᴹ : fooᴹ U₂ᴹ      ≡ U₁ᴹ
      fooElᴹ : fooᴹ (Elᴹ bᴹ) ≡ Elᴹ bᴹ

      Zᴹ  : Bᴹ U₁ᴹ Z
      apᴹ : Bᴹ {a = a} aᴹ b → Bᴹ (fooᴹ aᴹ) (ap b)

  module ActualElim (𝕞 : Methods) where
    open Methods 𝕞

    elim-A : ∀ a → Aᴹ a
    elim-B : ∀ b → Bᴹ (elim-A a) b

    elim-A U₁     = U₁ᴹ
    elim-A U₂     = U₂ᴹ
    elim-A (El b) = Elᴹ (elim-B b)

    elim-B Z      = Zᴹ
    elim-B (ap {a = U₁}   b) 
      = subst (λ aᴹ → Bᴹ aᴹ (ap b)) fooU₁ᴹ (apᴹ (elim-B b))
    elim-B (ap {a = U₂}   b)
      = subst (λ aᴹ → Bᴹ aᴹ (ap b)) fooU₂ᴹ (apᴹ (elim-B b))
    elim-B (ap {a = El a} b) 
      = subst (λ aᴹ → Bᴹ aᴹ (ap b)) fooElᴹ (apᴹ (elim-B b))

-- The problem with this eliminator is just that it is pretty inconvenient to
-- use...

module BadElimExample where
  open BadElim
  open ActualElim
  open Motive
  open Methods

  -- Like the original datatype, this eliminator is somewhat meaningless. Just
  -- an example.
  set-𝕄 : Motive 1ℓ 0ℓ
  set-𝕄 .Aᴹ _ = Set
  set-𝕄 .Bᴹ Aᴹ _ = Aᴹ

  set-𝕞 : Methods set-𝕄
  set-𝕞 .U₁ᴹ       = Bool
  set-𝕞 .U₂ᴹ       = ℕ
  set-𝕞 .Elᴹ false = ⊥
  set-𝕞 .Elᴹ true  = ⊤
  set-𝕞 .Zᴹ = false
  -- Note the implementation of 'fooᴹ' is pretty-much fixed based on the 
  -- equations. But we are still forced to write out the cases.
  set-𝕞 .fooᴹ {a = U₁} _    = set-𝕞 .U₂ᴹ
  set-𝕞 .fooᴹ {a = U₂} _    = set-𝕞 .U₁ᴹ
  set-𝕞 .fooᴹ {a = El b} aᴹ = aᴹ
  set-𝕞 .fooU₁ᴹ = refl
  set-𝕞 .fooU₂ᴹ = refl
  set-𝕞 .fooElᴹ = refl
  
  -- We have lost the evidence that 'bᴹ' is a boolean, so we can't match on it
  -- and do computation in the 'apᴹ' case!
  -- Maybe we could recover this information with extra proofs about 
  -- 'elim-A'/'elim-B' but clearly this is getting quite messy.
  -- Can we do better?
  set-𝕞 .apᴹ {a = U₁}   bᴹ = zero
  set-𝕞 .apᴹ {a = U₂}   bᴹ = false
  set-𝕞 .apᴹ {a = El b} bᴹ = bᴹ

-- IMO, the problem with the above induction principle was that we let the
-- caller define their own 'fooᴹ', but the computational behaviour of 'fooᴹ'
-- on the *range* of the eliminator is already fully defined by the equations!
--
-- Can we keep track of how elements produced by the eliminator are in its
-- range, and use this evidence to implement 'fooᴹ' generically?
module FancyElim {ℓ₁} {ℓ₂} (𝕄 : Motive ℓ₁ ℓ₂) where 
  open Motive 𝕄

  variable
    aᴹ a₁ᴹ a₂ᴹ : Aᴹ a
    bᴹ b₁ᴹ b₂ᴹ : Bᴹ aᴹ b

  record Methods : Set (ℓ₁ ⊔ ℓ₂)
  
  elim-A : Methods → ∀ a → Aᴹ a
  elim-B : (𝕞 : Methods) → ∀ b → Bᴹ (elim-A 𝕞 a) b

  -- 'Aᴹ' restricted to the range of 'elim-A'
  record Aᴱ (𝕞 : Methods) (a : A) : Set (ℓ₁ ⊔ ℓ₂) where
    constructor _,_
    eta-equality
    field
      A-out : Aᴹ a
      A-coh : elim-A 𝕞 a ≡ A-out
  open Aᴱ public

  -- We will try and implement 'fooᴱ' totally on the range of 'elim-A'
  fooᴱ : ∀ 𝕞 → Aᴱ 𝕞 a → Aᴱ 𝕞 (foo a)

  -- Note that as 'fooᴱ' will rely on calling on the eliminator, the 'Methods'
  -- needs to be able to have a forward reference to itself. Luckily, this is 
  -- actually possible with coinduction!
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

  -- And finally our fancy eliminator!
  elim-B 𝕞 Z      = 𝕞 .Zᴹ
  -- We need to inline 'foo' here to satisfy Agda's termination checker...
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

module FancyElimExample where
  open FancyElim public
  open Motive public
  open Methods using (methods; eq) public
  open PreMethods public

  -- Again, a somewhat meaningless example, just to demonstrate the eliminator
  -- works as we want.
  set-𝕄 : Motive 1ℓ 0ℓ
  set-𝕄 .Aᴹ _ = Set
  set-𝕄 .Bᴹ Aᴹ _ = Aᴹ

  -- Note we don't need any case for 'fooᴹ' here!
  set-𝕞 : Methods set-𝕄
  set-𝕞 .methods .self      = set-𝕞
  set-𝕞 .eq                 = refl
  set-𝕞 .methods .U₁ᴹ       = Bool
  set-𝕞 .methods .U₂ᴹ       = ℕ
  set-𝕞 .methods .Elᴹ false = ⊥
  set-𝕞 .methods .Elᴹ true  = ⊤
  set-𝕞 .methods .Zᴹ = false
  -- Our evidence that 'aᴹ' is in the range of 'elim-A' is sufficient to tell
  -- us that bᴹ here is indeed a boolean. We can match on our previous result
  -- and have the 'apᴹ' case do real computation!
  set-𝕞 .methods .apᴹ {a = U₁}   {aᴱ = aᴹ , refl} false = 1
  set-𝕞 .methods .apᴹ {a = U₁}   {aᴱ = aᴹ , refl} true  = 0
  set-𝕞 .methods .apᴹ {a = U₂}   {aᴱ = aᴹ , refl} bᴹ    = even bᴹ
  set-𝕞 .methods .apᴹ {a = El b} {aᴱ = aᴹ , refl} bᴹ    = bᴹ
        
  test : elim-B set-𝕄 set-𝕞 (ap (ap Z)) ≡ false
  test = refl 

-- TODO: Implement a translation between the different 'Methods' (I'm not sure
-- whether fancy 'Methods' can be translated into the earlier ones, but
-- the other direction should definitely be doable) and prove that this
-- translation is sound w.r.t. 'elim-A'/'elim-B'
