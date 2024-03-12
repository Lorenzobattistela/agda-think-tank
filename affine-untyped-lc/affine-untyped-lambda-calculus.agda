module affine-untyped-lc.affine-untyped-lambda-calculus

import Relation.Binary.PropositionalEquality as Eq
-- open Eq using (_≡_; refl)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (ℕ; zero; suc; _<_; _≤?_; z≤n; s≤s)
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Decidable using (True; toWitness)
open import Data.String using (String; _≟_)
open import Data.Bool using (Bool; true; false; T; not)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)

-- Variable names
Name : Set
Name = String

-- Affine lambda terms
data Term : Set where
  var : Name → Term
  _·_ : Term → Term → Term
  ƛ_⇒_ : Name → Term → Term

-- Substitution function
subst : Name → Term → Term → Term
subst x s (var y) with x ≟ y
... | yes _ = s
... | no  _ = var y
subst x s (t · u) = subst x s t · subst x s u
subst x s (ƛ y ⇒ t) with x ≟ y
... | yes _ = ƛ y ⇒ t
... | no  _ = ƛ y ⇒ subst x s t

-- Single-step reduction relation
infix 2 _—→_
data _—→_ : Term → Term → Set where
  ξ-·₁ : ∀ {t t' u} → t —→ t' → t · u —→ t' · u
  ξ-·₂ : ∀ {t u u'} → u —→ u' → t · u —→ t · u'
  β-ƛ : ∀ {x t u} → (ƛ x ⇒ t) · u —→ subst x u t

-- Reflexive-transitive closure of reduction
infix  2 _—↠_
infix 1 begin_
infixr 2 _—→⟨_⟩_
infix 3 _∎

data _—↠_ : Term → Term → Set where
  _∎ : ∀ t → t —↠ t
  _—→⟨_⟩_ : ∀ t {u v} → t —→ u → u —↠ v → t —↠ v

begin_ : ∀ {t u} → t —↠ u → t —↠ u
begin t—↠u = t—↠u

-- infix  4  _⊢_
-- infix  4  _∋_
-- infixl 5  _,_⦂_⁇_

-- infix  6  ƛ_
-- infix  6  ′_
-- infixl 7  _·_

-- Id : Set
-- Id = String

-- Used : Set
-- Used = Bool

-- data Type : Set where
--   ★ : Type

-- data Term : Set where
--   Lambda : Term → Term
--   Application : Term → Term
--   Variable : Term

-- data Context : Set where
--   ∅   : Context
--   _,_∶_ : Context → Id → Type → Context

-- removeFromContext : ∀ {n} → Context → Id → Context
-- removeFromContext ∅ _ = ∅


-- consume : Context → Id → Context

-- -- data _∋_ : Context → Type → Set where
-- --   Z : ∀ {Γ A}
-- --      ---------
-- --    → Γ , A ∋ A

-- --   S_ : ∀ {Γ A B}
-- --     → Γ ∋ A
-- --       ---------
-- --     → Γ , B ∋ A
  
-- -- infix 4 _⊢_⦂_⁇_