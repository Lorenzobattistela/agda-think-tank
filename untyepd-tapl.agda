
open import Data.String using (String; _≈?_)
open import Data.Bool using (if_then_else_; Bool; true; false)
open import Data.List hiding (deduplicate)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Data.Product using (_×_;_,_)

--------------------------------------------------------------------------------
--                                                                            
-- Helper Functions
--                                                                            
--------------------------------------------------------------------------------

-- Identifiers are just strings
Id : Set
Id = String

-- _∈?ᵇ_ : (e : Id) → (set : List Id) → Bool
-- e ∈?ᵇ [] = false
-- e ∈?ᵇ (x ∷ set) with e ≈? x
-- ... | yes _ = true
-- ... | no  _ = e ∈?ᵇ set

-- remove : List Id → Id → List Id
-- remove [] id = []
-- remove (x ∷ xs) id = if ⌊ x ≈? id ⌋ then xs else (remove xs id)

-- deduplicate : List Id → List Id
-- deduplicate [] = []
-- deduplicate (x ∷ xs) with x ∈?ᵇ xs
-- ... | false = x ∷ deduplicate xs
-- ... | true = deduplicate xs


-- --------------------------------------------------------------------------------
-- --                                                                            
-- -- Language Definition                                                        
-- --                                                                            
-- --------------------------------------------------------------------------------

-- -- We define our language with these terms
-- data Term : Set where
--   `_   : Id → Term
--   ƛ_⇒_ : Id → Term → Term
--   _·_  : Term → Term → Term

-- -- We only have one value
-- data Value : Term → Set where
--   λ-Abstraction : ∀ {x t} → Value (ƛ x ⇒ t)


-- -- Defining free variables in a term
-- FV : Term → List Id
-- FV (` x) = [ x ]
-- FV (ƛ x ⇒ t) = remove (FV t) x
-- FV (t₁ · t₂) = deduplicate ((FV t₁) ++ (FV t₂))

-- -- Defining subsitution
-- [_↦_]_ : Id → Term → Term → Term
-- [ x ↦ s ] (` y) with x ≈? y
-- ... | yes _ = s
-- ... | no  _ = ` y
-- [ x ↦ s ] (ƛ y ⇒ t) with x ≈? y
-- ... | yes x≈y = (ƛ y ⇒ t)
-- ... | no  x≉y = if (y ∈?ᵇ FV(s)) then (ƛ y ⇒ t) else (ƛ y ⇒ ([ x ↦ s ] t))
-- [ x ↦ s ] (t₁ · t₂) =  ([ x ↦ s ] t₁) · ([ x ↦ s ] t₂)

-- -- Defining the evaluation rules
-- data _⟶_ : Term → Term → Set where
--   E-APP1 : ∀ {t₁ t₁' t₂} → t₁ ⟶ t₁' → (t₁ · t₂) ⟶ (t₁' · t₂)
--   E-APP2 : ∀ {v t t'} → Value v → t ⟶ t' → (v · t) ⟶ (v · t')
--   E-APPABS : ∀ {v t} {x : Id} → Value v → ((ƛ x ⇒ t) · v) ⟶ ([ x ↦ v ] t)

data Affine : Set where
  ε : Affine
  _+_ : Affine -> Affine -> Affine

zero : Affine -> Bool
zero ε = false
zero (_ + _) = true

Ctx : Set
Ctx = List (Id × Affine)

_⊎_ : Ctx -> (Id × Affine) -> Ctx
Γ ⊎ x = x ∷ Γ

data Term : Ctx -> Set where
  var : ∀ {Γ} -> (x : Id) -> (u : Affine) -> Term (Γ ⊎ (x , u))
  abs : ∀ {Γ} -> (x : Id) -> (M : Term Γ) -> Term Γ
  app : ∀ {Γ} -> (M N : Term Γ) -> Term Γ


-- valid : (x : Id) -> (Γ : Ctx) -> Bool
-- valid x [] = false
-- valid x ((x₁ , _) ∷ xs) with x₁ ≟ x
-- ... | yes _ = true
-- ... | no _ = valid x xs

delete : (x : Id) -> (Γ : Ctx) -> Ctx
delete x [] = []
delete x ((x₁ , u) :: xs) with x₁ Data.String.≟ x
... | yes _ = delete x xs
... | no _ = (x₁ , u) :: delete x xs

-- -- Deduplicate context (used in application rule)
-- deduplicate : Ctx -> Ctx
-- deduplicate [] = []
-- deduplicate ((x , u₁) :: xs) with find x xs
-- ... | nothing = (x , u₁) :: deduplicate xs
-- ... | just (_ , u₂) = deduplicate ((x , u₁ + u₂) :: delete x xs)


-- Evaluation rules
data Step : ∀ {Γ} -> Term Γ -> Term Γ -> Set where
    app₁  : ∀ {Γ M₁ M₂ N} -> Step {Γ} M₁ M₂ -> Step (app M₁ N) (app M₂ N)
    app₂  : ∀ {Γ M N₁ N₂} -> Step {Γ} N₁ N₂ -> Step (app M N₁) (app M N₂)
    βstep : ∀ {Γ x M N} -> Step {Γ} (app (abs x M) (var x N)) (delete x M)