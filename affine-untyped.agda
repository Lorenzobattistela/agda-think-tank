
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (ℕ; zero; suc; _<_; _≤?_; z≤n; s≤s)
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Decidable using (True; toWitness)

-- terms syntax:
-- variables: `x
-- abstractions: ƛ x => N
-- applications: L @ M

data Term : Set where
  Var : ℕ → Term
  Lam : (n : ℕ) → Term → Term
  App : Term → Term → Term

infix  4  _⊢_
infix  4  _∋_
infixl 5  _,_

infix  6  ƛ_
infix  6  ′_
infixl 7  _·_

data Type : Set where
  ★ : Type