import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (ℕ; zero; suc; _<_; _≤?_; z≤n; s≤s)
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Decidable using (True; toWitness)

infix  4  _⊢_
infix  4  _∋_
infixl 5  _,_

infix  6  ƛ_
infix  6  ′_
infixl 7  _·_

-- we have just one type (untyped is uni-typed)
data Type : Set where
  ★ : Type

-- Show that Type is isomorphic to ⊤, the unit type.
infix 0 _≃_
record _≃_ (A B : Set) : Set where
  field
    to   : A → B
    from : B → A
    from∘to : ∀ (x : A) → from (to x) ≡ x
    to∘from : ∀ (y : B) → to (from y) ≡ y
open _≃_

data ⊤ : Set where

  tt :
    --
    ⊤

record Type≃⊤ : Set where
    field
        to : Type → ⊤
        from : ⊤ → Type
        from∘to : ∀ (x : Type) → from (to x) ≡ x
        to∘from : ∀ (y : ⊤) → to (from y) ≡ y


--  a context is a list of types, with the type of the most recently bound variable on the right. (we can use something here to make it affine)

data Context : Set where
  ∅   : Context
  _,_ : Context → Type → Context

-- Show that Context is isomorphic to ℕ.
record Context≃ℕ : Set where
    field
        to : Context → ℕ
        from : ℕ → Context
        from∘to : ∀ (x : Context) → from (to x) ≡ x
        to∘from : ∀ (y : ℕ) → to (from y) ≡ y


-- Intrinsically-scoped variables correspond to the lookup judgment.

data _∋_ : Context → Type → Set where

  Z : ∀ {Γ A}
     ---------
   → Γ , A ∋ A

  S_ : ∀ {Γ A B}
    → Γ ∋ A
      ---------
    → Γ , B ∋ A

-- We could write the rules with all instances of A and B replaced by ★, but arguably it is clearer not to do so.
-- Because ★ is the only type, the judgment doesn’t guarantee anything useful about types. But it does ensure that all variables are in scope. For instance, we cannot use S S Z in a context that only binds two variables.

-- Intrinsically-scoped terms correspond to the typing judgment, but with ★ as the only type. The result is that we check that terms are well scoped — that is, that all variables they mention are in scope — but not that they are well typed:

data _⊢_ : Context → Type → Set where

  `_ : ∀ {Γ A}
    → Γ ∋ A
      -----
    → Γ ⊢ A

  ƛ_  :  ∀ {Γ}
    → Γ , ★ ⊢ ★
      ---------
    → Γ ⊢ ★

  _·_ : ∀ {Γ}
    → Γ ⊢ ★
    → Γ ⊢ ★
      ------
    → Γ ⊢ ★

-- writing variables as numerals: we can convert a natural to the corresponding de bruijn index. We no longer need to lookup the etype in the context since every variable has the same type (what whe could do in affine is lookup the context to check the usage)

length : Context → ℕ
length ∅        =  zero
length (Γ , _)  =  suc (length Γ)

count : ∀ {Γ} → {n : ℕ} → (p : n < length Γ) → Γ ∋ ★
count {Γ , ★} {zero}    (s≤s z≤n)  =  Z
count {Γ , ★} {(suc n)} (s≤s p)    =  S (count p)

-- We can then introduce a convenient abbreviation for variables:

#_ : ∀ {Γ}
  → (n : ℕ)
  → {n∈Γ : True (suc n ≤? length Γ)}
    --------------------------------
  → Γ ⊢ ★
#_ n {n∈Γ}  =  ` count (toWitness n∈Γ)

-- computing two plus two on church numerals
twoᶜ : ∀ {Γ} → Γ ⊢ ★
twoᶜ = ƛ ƛ (# 1 · (# 1 · # 0))

fourᶜ : ∀ {Γ} → Γ ⊢ ★
fourᶜ = ƛ ƛ (# 1 · (# 1 · (# 1 · (# 1 · # 0))))

plusᶜ : ∀ {Γ} → Γ ⊢ ★
plusᶜ = ƛ ƛ ƛ ƛ (# 3 · # 1 · (# 2 · # 1 · # 0))

2+2ᶜ : ∅ ⊢ ★
2+2ᶜ = plusᶜ · twoᶜ · twoᶜ

-- computing one plus one on church numerals
oneᶜ : ∀ {Γ} → Γ ⊢ ★
oneᶜ = ƛ ƛ (# 1 · # 0)

1+1ᶜ : ∅ ⊢ ★
1+1ᶜ = plusᶜ · oneᶜ · oneᶜ

