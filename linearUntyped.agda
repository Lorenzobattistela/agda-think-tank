import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (ℕ; zero; suc; _<_; _≤?_; z≤n; s≤s)
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Decidable using (True; toWitness)
open import Data.Product using (_×_)
open import Data.Bool using (if_then_else_; Bool; true; false)

-- infix  4  _⊢_
-- infix  4  _∋_
-- infixl 5  _,_

-- infix  6  ƛ_
-- infix  6  ′_
-- infixl 7  _·_

-- how to make this affine?
-- if context holds a pair (type, bool) where bool is a bool flag that indicates wether a variable is used or not
-- since in this system it is using de brujin we already have indexes to identify variables
-- then for reductions we need to check for possible duplication?
-- maybe we use record for context? guess no, they have to be the same type? No. can use different types

data Type : Set where
  * : Type

-- record Test (A B : Bool) : Set where
--     field
--         fst : A
--         snd : B


record Pair (A B : Set) : Set where
  field
    fst : A
    snd : B

context_pair : Pair Bool Type
context_pair = record { fst = false; snd = *}

-- now how do we put this record in there?

-- maybe just use x

data Context : Set where
  ∅   : Context
  _,_ : Context → (Type × Bool) → Context

a : Context 
a = ∅ , (* , true)

-- data _∋_ : Context → Type → Set where

--   Z : ∀ {Γ A}
--      ---------
--    → Γ , A ∋ A

--   S_ : ∀ {Γ A B}
--     → Γ ∋ A
--       ---------
--     → Γ , B ∋ A