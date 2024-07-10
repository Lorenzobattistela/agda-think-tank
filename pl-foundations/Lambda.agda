module pl-foundations.Lambda where

open import Data.Bool using (Bool; true; false; T; not)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; _∷_; [])
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (∃-syntax; _×_)
open import Data.String using (String; _≟_)
open import Data.Unit using (tt)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Nullary.Decidable using (False; toWitnessFalse)
open import Relation.Nullary.Negation using (¬?)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)

-- syntax:
-- terms have seven constructs: 3 for the core lambda calculi
-- Variables: ‵ x
-- Abstractions ƛ x ⇒ N
-- Applications: L ∙ M
-- 3 for the naturals
-- Zero: ‵zero
-- successor ‵suc M
-- Case: case L [zero ⇒ M | suc x ⇒ N ]
-- And one for recursion:
-- Fixpoint μ x ⇒ M
-- With the exception of variables and fixpoints, each term form either constructs a value of a given type (abstractions yield functions, zero and successor yield natural numbers) or deconstructs it (applications use functions, case terms use naturals). We will see this again when we come to rules for assigning types to terms, where constructors correspond to introduction rules and deconstructors to eliminators
-- Syntax of terms in BNF:
-- L, M, N  ::=
-- ` x  |  ƛ x ⇒ N  |  L · M  |
-- `zero  |  `suc M  |  case L [zero⇒ M |suc x ⇒ N ]  |
-- μ x ⇒ M

Id : Set
Id = String

infix  5  ƛ_⇒_
infix  5  μ_⇒_
infixl 7  _·_
infix  8  `suc_
infix  9  `_

data Term : Set where
  `_                      :  Id → Term
  ƛ_⇒_                    :  Id → Term → Term
  _·_                     :  Term → Term → Term
  `zero                   :  Term
  `suc_                   :  Term → Term
  case_[zero⇒_|suc_⇒_]    :  Term → Term → Id → Term → Term
  μ_⇒_                    :  Id → Term → Term













