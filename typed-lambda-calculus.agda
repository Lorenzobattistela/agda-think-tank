open import Data.Bool using (Bool; true; false; T; not)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; _∷_; [])
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (∃-syntax; _×_)
open import Data.String using (String; _≟_)
open import Data.Unit using (tt)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Nullary.Decidable using (False; toWitnessFalse)
-- open import Relation.Nullary.Negation using (¬?)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)

-- terms syntax:
-- variables: `x
-- abstractions: ƛ x => N
-- applications: L @ M
-- naturals:
-- zero: `zero
-- succesor: `suc M
-- case: case L [zero => M | suc x => N]
-- one for recursion: fixpoint: μ x => M

