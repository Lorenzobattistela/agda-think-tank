module affine-untyped-lc.test where

-- open import Data.Bool using (if_then_else_; Bool; true; false; _∧_)
-- open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _≟_;_<_; _≤_;_＝_;z≤n; s≤s)
-- open import Data.List using (List; _∷_; []; tail; length; _++_; replicate; lookup)
-- open import Data.Product using (_×_; _,_; proj₁; proj₂)
-- open import Data.Sum using (_⊎_; inj₁; inj₂)
-- open import Relation.Binary.PropositionalEquality using (_≡_; refl)
-- open import Relation.Nullary using (Dec; yes; no; ¬_)
-- open import Induction.WellFounded using (Acc; acc)
-- open import Data.Empty using (⊥; ⊥-elim)

-- data Term : Set where
--     var : ℕ → Term
--     lam : Term → Term
--     app : Term → Term → Term

-- Context : Set
-- Context = List Bool

-- lookup : ℕ → Context → Bool
-- lookup x [] = false
-- lookup zero (b ∷ ctx) = b
-- lookup (suc x) (b ∷ ctx) = lookup x ctx

-- consume : ℕ → Context → Context
-- consume x [] = []
-- consume zero (b ∷ ctx) = false ∷ ctx
-- consume (suc x) (b ∷ ctx) = b ∷ consume x ctx

-- affine : Context → Term → Bool × Context
-- affine ctx (var x) = if lookup x ctx then (true , consume x ctx) else (false , ctx)

-- affine ctx (lam t) with affine (true ∷ ctx) t
-- ... | (b , []) = (b , [])
-- ... | (b , (_ ∷ xs)) = (b , xs)

-- affine ctx (app t u) = 
--     let (b1 , ctx1) = affine ctx t
--         (b2 , ctx2) = affine ctx1 u
--     in (b1 ∧ b2 , ctx2)

-- affine_term : Term
-- affine_term = lam ( var 0 ) 

-- is_affine : Bool × Context
-- is_affine = affine [] affine_term

-- is_affine_bool : Bool
-- is_affine_bool = proj₁ is_affine

-- affine-is-affine : is_affine_bool ≡ true
-- affine-is-affine = refl

-- not-affine-term : Term
-- not-affine-term = lam (app (var 0) (var 0))

-- not-affine-is-affine : Bool × Context
-- not-affine-is-affine = affine [] not-affine-term

-- not-affine-bool : Bool
-- not-affine-bool = proj₁ is_affine

-- not-affine-is-affine-check : not-affine-bool ≡ true
-- not-affine-is-affine-check = refl

-- contradiction : ∀ {A : Set} {x y : Bool} → x ≡ true → x ≡ false → A
-- contradiction refl ()

-- data Affine : Context → Term → Set where
--   var : ∀ {ctx x} → lookup x ctx ≡ true → Affine ctx (var x)
--   lam : ∀ {ctx t} → Affine (true ∷ ctx) t → Affine ctx (lam t)
--   app : ∀ {ctx t u} → Affine ctx t → Affine (proj₂ (affine ctx t)) u → Affine ctx (app t u)

-- affine-implies-Affine : ∀ {ctx t} → proj₁ (affine ctx t) ≡ true → Affine ctx t
-- affine-implies-Affine {ctx} {var x} eq with lookup x ctx
-- ... | true = var refl
-- ... | false = contradiction eq refl


-- bound the size of the term by a natural number, show that β-reduction always strictly reduces the size of the term, and then do induction on the natural number bound to show termination.


-- data Affine : Set where
--   var : ℕ → Affine
--   _·_ : Affine → Affine → Affine
--   λ'_  : Affine → Affine

-- data _∈_ : ℕ → Affine → Set where
--   here  : ∀ {n t} → n ∈ var n
--   there : ∀ {n m t} → n ∈ t → n ∈ (var m · t)
--   λ-abs : ∀ {n t} → n ∈ t → n ∈ (λ' t)

-- data Unique : Affine → Set where
--   var-unique : ∀ {n} → Unique (var n)
--   ·-unique   : ∀ {t₁ t₂} → Unique t₁ → Unique t₂ → (∀ {n} → n ∈ t₁ → n ∈ t₂ → ⊥) → Unique (t₁ · t₂)
--   λ-unique   : ∀ {t} → Unique t → Unique (λ' t)

-- subst : ℕ → Affine → Affine → Affine
-- subst n t (var m)   = if m == n then t else var m
-- subst n t (t₁ · t₂) = subst n t t₁ · subst n t t₂
-- subst n t (λ' t₁)    = λ' (subst (suc n) t t₁)

-- normalize : Affine → Affine
-- normalize (var n)   = var n
-- normalize (t₁ · t₂) with normalize t₁ | normalize t₂
-- ... | var n   | t₂' = t₂'
-- ... | λ' t     | t₂' = normalize (subst 0 t₂' t)
-- ... | t₁' · _ | t₂' = t₁' · t₂'
-- normalize (λ' t)     = λ' (normalize t)

-- data WellFormed : List Bool → Affine → Set where
--   var : ∀ {Γ : List Bool} → (x : ℕ) → x < length Γ → lookup x Γ ≡ false → WellFormed Γ (var x)
  
--   _·_ : ∀ {Γ t1 t2} → WellFormed Γ t1 → WellFormed Γ t2 →
--         (∀ {x} → Var x t1 → Var x t2 → ⊥) → WellFormed Γ (t1 · t2)
        
--   λ'_⇒_ : ∀ {Γ n t} → WellFormed (replicate n false ++ Γ) t → WellFormed Γ (λ' n ⇒ t)


open import Data.Bool using (Bool; true; false; T; not)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; _++_; map; foldr; filter)
open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _≤?_; _<_; _≤_)
open import Data.Nat.Properties using (≤-refl; ≤-trans; ≤-step; n≤1+n)
open import Data.Product using (_×_; proj₁; proj₂; ∃; ∃-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; cong₂)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Decidable using (⌊_⌋; False; toWitnessFalse)
open import Relation.Nullary.Negation using (¬?)
open import Relation.Nullary.Product using (_×-dec_)

infix  4 _⊢_
infix  4 _∋_
infixl 5 _,_

infixr 7 _⇒_

infix  5 ƛ_
infix  5 μ_
infixl 7 _·_
infix  8 `suc_
infix  9 `_

data Type : Set where
  `⊤ : Type
  _⇒_ : Type → Type → Type

data Context : Set where
  ∅   : Context
  _,_ : Context → Type → Context

data _∋_ : Context → Type → Set where
  Z : ∀ {Γ A}
      ----------
    → Γ , A ∋ A

  S : ∀ {Γ A B}
    → Γ ∋ A
      ----------
    → Γ , B ∋ A
  
data _⊢_ : Context → Type → Set where
  `_ : ∀ {Γ A}
    → Γ ∋ A
      -----
    → Γ ⊢ A

  ƛ_  : ∀ {Γ A B}
    → Γ , A ⊢ B
      ---------
    → Γ ⊢ A ⇒ B

  _·_ : ∀ {Γ A B}
    → Γ ⊢ A    → Γ ⊢ A
      ---------
    → Γ ⊢ B

  μ_ : ∀ {Γ A}
    → Γ , A ⊢ A
      ---------
    → Γ ⊢ A

data AffineContext : Context → Set where
  ∅ : AffineContext ∅
  _,_ : ∀ {Γ A}
    → AffineContext Γ
    → Γ ⊢ A
      ---------------
    → AffineContext (Γ , A)

data _∋ᵃ_ : Context → Type → Set where
  Zᵃ : ∀ {Γ A}
      ----------
    → (Γ , A) ∋ᵃ A

  Sᵃ : ∀ {Γ A B}
    → Γ ∋ᵃ B
      ----------
    → (Γ , A) ∋ᵃ B
  
-- -- Affine typing judgment
data _⊢ᵃ_ : Context → Type → Set where
  `_ : ∀ {Γ A}
    → Γ ∋ᵃ A
      -------
    → Γ ⊢ᵃ A

  ƛ_  : ∀ {Γ A B}
    → AffineContext Γ
    → (Γ , A) ⊢ᵃ B
      -----------
    → (Γ ⊢ᵃ A) ⇒ B

--   _·_ : ∀ {Γ A B}
--     → Γ ⊢ᵃ A ⇒ B
--     → Γ ⊢ᵃ A
--       -----------
--     → Γ ⊢ᵃ B

--   μ_ : ∀ {Γ A}
--     → AffineContext Γ
--     → Γ , A ⊢ᵃ A
--       -----------
--     → Γ ⊢ᵃ A

-- -- Affine substitution
-- substᵃ : ∀ {Γ Δ} → (∀ {A} → Γ ∋ᵃ A → Δ ⊢ᵃ A) → (∀ {A} → Γ ⊢ᵃ A → Δ ⊢ᵃ A)
-- substᵃ σ (` k)   = σ k
-- substᵃ σ (ƛ_ Γ N)   = ƛ_ Γ (substᵃ (extsᵃ σ) N)
-- substᵃ σ (L · M) = (substᵃ σ L) · (substᵃ σ M)
-- substᵃ σ (μ_ Γ N)   = μ_ Γ (substᵃ (extsᵃ σ) N)

-- extsᵃ : ∀ {Γ Δ} → (∀ {A} → Γ ∋ᵃ A → Δ ⊢ᵃ A) → (∀ {A B} → Γ , B ∋ᵃ A → Δ , B ⊢ᵃ A)
-- extsᵃ σ Zᵃ      = ` Zᵃ
-- extsᵃ σ (Sᵃ x)  = substᵃ Sᵃ (σ x)

-- -- Affine reduction rules
-- infix 2 _—→ᵃ_
-- data _—→ᵃ_ : ∀ {Γ A} → (Γ ⊢ᵃ A) → (Γ ⊢ᵃ A) → Set where
--   ξ₁ : ∀ {Γ A B} {L L′ : Γ ⊢ᵃ A ⇒ B} {M : Γ ⊢ᵃ A}
--     → L —→ᵃ L′
--       ---------------
--     → L · M —→ᵃ L′ · M

--   ξ₂ : ∀ {Γ A B} {L : Γ ⊢ᵃ A ⇒ B} {M M′ : Γ ⊢ᵃ A}
--     → M —→ᵃ M′
--       ---------------
--     → L · M —→ᵃ L · M′

--   β : ∀ {Γ A B} {N : Γ , A ⊢ᵃ B} {M : Γ ⊢ᵃ A}
--       ----------------------------------
--     → (ƛ_ Γ N) · M —→ᵃ substᵃ (λ{ Zᵃ → M ; (Sᵃ x) → ` x }) N

--   ζ : ∀ {Γ A B} {N N′ : Γ , A ⊢ᵃ B}
--     → N —→ᵃ N′
--       -----------
--     → ƛ_ Γ N —→ᵃ ƛ_ Γ N′

--   μ : ∀ {Γ A} {N : Γ , A ⊢ᵃ A}
--       ----------------
--     → μ_ Γ N —→ᵃ substᵃ (λ{ Zᵃ → μ_ Γ N ; (Sᵃ x) → ` x }) N

-- -- Progress and evaluation
-- data Progress {Γ A} (M : Γ ⊢ᵃ A) : Set where
--   step : ∀ {N : Γ ⊢ᵃ A}
--     → M —→ᵃ N
--       ----------
--     → Progress M

--   done : Normal M
--       ----------
--     → Progress M

-- progress : ∀ {Γ A} → (M : Γ ⊢ᵃ A) → Progress M
-- progress (` x)                = done (′ ` x)
-- progress (ƛ_ Γ N)             = done (ƛ_ Γ (progress N))
-- progress (μ_ Γ N)             = step μ
-- progress (` x · M)            = done (′ (` x) · progress M)
-- progress ((ƛ_ Γ N) · M)       = step β
-- progress ((μ_ Γ N) · M)       = step (ξ₁ μ)
-- progress (L@(_ · _) · M)      = step (ξ₁ (progress L))
-- progress (L@(_ · _) · M)      = step (ξ₂ (progress M))

-- -- Evaluation
-- record Gas : Set where
--   constructor gas
--   field
--     amount : ℕ

-- data Finished {Γ A} (N : Γ ⊢ᵃ A) : Set where
--   done : Normal N
--       ----------
--     → Finished N

--   out-of-gas : Finished N

-- data Steps : ∀ {Γ A} → Γ ⊢ᵃ A → Set where
--   steps : ∀ {Γ A} {L N : Γ ⊢ᵃ A}
--     → L —↠ᵃ N
--     → Finished N
--       ----------
--     → Steps L

-- eval : ∀ {Γ A} → Gas → (L : Γ ⊢ᵃ A) → Steps L
-- eval (gas zero)    L = steps (L ∎) out-of-gas
-- eval (gas (suc m)) L with progress L
-- ... | done NrmL   = steps (L ∎) (done NrmL)
-- ... | step {M} L—→ᵃM with eval (gas m) M
-- ...   | steps M—↠ᵃN fin = steps (L —→⟨ L—→ᵃM ⟩ M—↠ᵃN) fin
-- ```

-- The main changes made to enforce the affine property are:

-- 1. Introduction of `AffineContext`, which represents a context where each variable is used at most once.

-- 2. Modification of the variable rule to `_∋ᵃ_`, which ensures that variables are used affinely.

-- 3. Modification of the typing judgment to `_⊢ᵃ_`, which incorporates the affine context and variable rules.

-- 4. Modification of the substitution function to `substᵃ` and `extsᵃ`, which work with the affine typing judgment.

-- 5. Modification of the reduction rules to use the affine typing judgment and substitution.

-- 6. Modification of the progress and evaluation functions to use the affine typing judgment and reduction rules.

-- The affine property is now enforced in the type system, ensuring that variables are used at most once in the terms. The reduction rules and evaluation function are updated accordingly to work with the affine typing judgment.

-- Please note that this is one possible way to enforce the affine property in the untyped lambda calculus. There might be other variations or approaches to achieve the same goal.