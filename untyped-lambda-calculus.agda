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


