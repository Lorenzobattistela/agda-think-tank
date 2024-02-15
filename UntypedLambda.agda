module UntypedLambda where

open import Data.String using (String; _≈?_)
open import Data.Bool using (if_then_else_; Bool; true; false)
open import Data.List hiding (deduplicate)
open import Data.Product using (_×_)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

--------------------------------------------------------------------------------
--                                                                            
-- Helper Functions
--                                                                            
--------------------------------------------------------------------------------

-- Identifiers are just strings
Id : Set
Id = String

_∈?ᵇ_ : (e : Id) → (set : List Id) → Bool
e ∈?ᵇ [] = false
e ∈?ᵇ (x ∷ set) with e ≈? x
... | yes _ = true
... | no  _ = e ∈?ᵇ set

remove : List Id → Id → List Id
remove [] id = []
remove (x ∷ xs) id = if ⌊ x ≈? id ⌋ then xs else (remove xs id)

deduplicate : List Id → List Id
deduplicate [] = []
deduplicate (x ∷ xs) with x ∈?ᵇ xs
... | false = x ∷ deduplicate xs
... | true = deduplicate xs


--------------------------------------------------------------------------------
--                                                                            
-- Language Definition                                                        
--                                                                            
--------------------------------------------------------------------------------

-- We define our language with these terms
data Term : Set where
  `_   : Id → Term
  ƛ_⇒_ : Id → Term → Term
  _·_  : Term → Term → Term
  !_ : Term → Term

-- We only have one value
data Value : Term → Set where
  λ-Abstraction : ∀ {x t} → Value (ƛ x ⇒ t)
  Linear : ∀ {t} → Value t → Value (! t)

-- Defining free variables in a term
FV : Term → List Id
FV (` x) = [ x ]
FV (ƛ x ⇒ t) = remove (FV t) x
FV (t₁ · t₂) = deduplicate ((FV t₁) ++ (FV t₂))
FV (! t) = FV t

-- Defining subsitution
[_↦_]_ : Id → Term → Term → Term
[ x ↦ s ] (` y) with x ≈? y
... | yes _ = s
... | no  _ = ` y
[ x ↦ s ] (ƛ y ⇒ t) with x ≈? y
... | yes x≈y = (ƛ y ⇒ t)
... | no  x≉y = if (y ∈?ᵇ FV(s)) then (ƛ y ⇒ t) else (ƛ y ⇒ ([ x ↦ s ] t))
[ x ↦ s ] (! t) = ! ([ x ↦ s ] t)
[ x ↦ s ] (t₁ · t₂) =  ([ x ↦ s ] t₁) · ([ x ↦ s ] t₂)

-- Defining the evaluation rules
data _⟶_ : Term → Term → Set where
  E-APP1 : ∀ {t₁ t₁' t₂} → t₁ ⟶ t₁' → (t₁ · t₂) ⟶ (t₁' · t₂)
  E-APP2 : ∀ {v t t'} → Value v → t ⟶ t' → (v · t) ⟶ (v · t')
  E-APPABS : ∀ {v t} {x : Id} → Value v → (v · (` x)) ⟶ (v · t) → ((ƛ x ⇒ t) · v) ⟶ ([ x ↦ v ] t)


linearVariable : Term → Id → Bool
linearVariable t x = count (FV t) x ≟ 1