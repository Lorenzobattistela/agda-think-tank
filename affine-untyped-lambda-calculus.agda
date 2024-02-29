import Relation.Binary.PropositionalEquality as Eq
-- open Eq using (_≡_; refl)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (ℕ; zero; suc; _<_; _≤?_; z≤n; s≤s)
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Decidable using (True; toWitness)
open import Data.String using (String; _≟_)
open import Data.Bool using (Bool; true; false; T; not)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)


infix  4  _⊢_
infix  4  _∋_
infixl 5  _,_⦂_⁇_

infix  6  ƛ_
infix  6  ′_
infixl 7  _·_

Id : Set
Id = String

Used : Set
Used = Bool

data Type : Set where
  ★ : Type

data Context : Set where
  ∅   : Context
  _,_⦂_⁇_ : Context → Id → Type → Used → Context

data _∋_⦂_⁇_ : Context → Id → Type → Used → Set where
    Z : ∀ {Γ x A U}
       ----------------
      → (Γ , x ⦂ A ⁇ U) ∋ x ⦂ A ⁇ U
