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


import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (ℕ; zero; suc; _<_; _≤?_; z≤n; s≤s)
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Decidable using (True; toWitness)
open import Data.Product using (_×_; ∃; ∃-syntax) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)

infix 4 _⊢_
infix 4 _∋_
infixl 5 _,_
infix 6 ƛ_
infix 6 ′_
infixl 7 _·_

data Type : Set where
  ★ : Type

data Context : Set where
  ∅ : Context
  _,_ : Context → Type → Context

data _∋_ : Context → Type → Set where
  Z : ∀ {Γ A}
    ---------
    → Γ , A ∋ A

  S_ : ∀ {Γ A B}
    → Γ ∋ A
    ---------
    → Γ , B ∋ A

data _⊢_ : Context → Type → Set where
  `_ : ∀ {Γ A}
    → Γ ∋ A
    -----
    → Γ ⊢ A

  ƛ_ : ∀ {Γ}
    → Γ , ★ ⊢ ★
    ---------
    → Γ ⊢ ★

  _·_ : ∀ {Γ}
    → Γ ⊢ ★
    → Γ ⊢ ★
    ------
    → Γ ⊢ ★

data Neutral : ∀ {Γ A} → Γ ⊢ A → Set
data Normal  : ∀ {Γ A} → Γ ⊢ A → Set

data Neutral where
  `_ : ∀ {Γ A} (x : Γ ∋ A)
    -------------
    → Neutral (` x)

  _·_ : ∀ {Γ} {L M : Γ ⊢ ★}
    → Neutral L
    → Normal M
    ---------------
    → Neutral (L · M)

data Normal where
  ′_ : ∀ {Γ A} {M : Γ ⊢ A}
    → Neutral M
    ---------
    → Normal M

  ƛ_ : ∀ {Γ} {N : Γ , ★ ⊢ ★}
    → Normal N
    ------------
    → Normal (ƛ N)

data _IsUsed_ : ∀ {Γ A} → Γ ∋ A → Γ ⊢ A → Set where
  `_ : ∀ {Γ A} (x : Γ ∋ A)
    -----------------
    → x IsUsed (` x)

  _·₁_ : ∀ {Γ} {x : Γ ∋ ★} {L : Γ ⊢ ★} {M : Γ ⊢ ★}
    → x IsUsed L
    -----------------
    → x IsUsed (L · M)

  _·₂_ : ∀ {Γ} {x : Γ ∋ ★} {L : Γ ⊢ ★} {M : Γ ⊢ ★}
    → x IsUsed M
    -----------------
    → x IsUsed (L · M)

_⊗_ : Context → Context → Context
∅ ⊗ Δ = Δ
(Γ , A) ⊗ Δ = (Γ ⊗ Δ) , A

data _⊢_⦂_ : Context → Context → Type → Set where
  `_ : ∀ {Γ Δ A}
    → Γ ∋ A
    → (x : Δ ∋ A)
    ---------------
    → Γ ⊢ Δ ⦂ A

  ƛ_ : ∀ {Γ Δ}
    → Γ , ★ ⊢ Δ ⦂ ★
    -----------------
    → Γ ⊢ Δ , ★ ⦂ ★

  _·_ : ∀ {Γ Δ Σ}
    → Γ ⊢ Δ ⦂ ★
    → Δ ⊢ Σ ⦂ ★
    ---------------
    → Γ ⊢ Σ ⦂ ★

-- data _—→_ : ∀ {Γ A} → (Γ ⊢ A) → (Γ ⊢ A) → Set where
--   ξ₁ : ∀ {Γ} {L L′ M : Γ ⊢ ★}
--     → L —→ L′
--     ----------------
--     → L · M —→ L′ · M

--   ξ₂ : ∀ {Γ} {L M M′ : Γ ⊢ ★}
--     → M —→ M′
--     ----------------
--     → L · M —→ L · M′

--   β : ∀ {Γ} {N : Γ , ★ ⊢ ★} {M : Γ ⊢ ★}
--     → (∀ {A} (x : Γ , ★ ∋ A) → x IsUsed N → A ≡ ★)
--     -------------------------------------------------
--     → (ƛ N) · M —→ N [ M ]

--   ζ : ∀ {Γ} {N N′ : Γ , ★ ⊢ ★}
--     → N —→ N′
--     -----------
--     → ƛ N —→ ƛ N′

-- infix 2 _—↠_
-- infix 1 begin_
-- infixr 2 _—→⟨_⟩_
-- infix 3 _∎

-- data _—↠_ {Γ A} : (Γ ⊢ A) → (Γ ⊢ A) → Set where
--   _∎ : (M : Γ ⊢ A)
--     ------
--     → M —↠ M

--   _—→⟨_⟩_ : (L : Γ ⊢ A) {M N : Γ ⊢ A}
--     → L —→ M
--     → M —↠ N
--     ---------
--     → L —↠ N

-- begin_ : ∀ {Γ A} {M N : Γ ⊢ A}
--   → M —↠ N
--   ---------
--   → M —↠ N
-- begin M—↠N = M—↠N

-- progress : ∀ {Γ A} → (M : Γ ⊢ A) → (∃[ N ] (M —→ N)) ⊎ Normal M
-- progress (` x) = inj₂ (′ (` x))
-- progress (ƛ N) with progress N
-- ... | inj₁ ⟨ N′ , N—→N′ ⟩ = inj₁ ⟨ ƛ N′ , ζ N—→N′ ⟩
-- ... | inj₂ NrmN = inj₂ (ƛ NrmN)
-- progress (` x · M) with progress M
-- ... | inj₁ ⟨ M′ , M—→M′ ⟩ = inj₁ ⟨ ` x · M′ , ξ₂ M—→M′ ⟩
-- ... | inj₂ NrmM = inj₂ (′ (` x) · NrmM)
-- progress ((ƛ N) · M) = inj₁ ⟨ N [ M ] , β (λ { Z → refl ; (S x) → ⊥-elim (¬∋ƛ· x) }) ⟩
--   where
--     ¬∋ƛ· : ∀ {Γ A B} (x : Γ ∋ B) → ¬ (x IsUsed (ƛ N · M))
--     ¬∋ƛ· x (() ·₁ _)
--     ¬∋ƛ· x (() ·₂ _)
-- progress (L@(_ · _) · M) with progress L
-- ... | inj₁ ⟨ L′ , L—→L′ ⟩ = inj₁ ⟨ L′ · M , ξ₁ L—→L′ ⟩
-- ... | inj₂ (′ NeuL) with progress M
-- ...   | inj₁ ⟨ M′ , M—→M′ ⟩ = inj₁ ⟨ L · M′ , ξ₂ M—→M′ ⟩
-- ...   | inj₂ NrmM = inj₂ (′ NeuL · NrmM)

-- normalize : ∀ {Γ A} → (M : Γ ⊢ A) → ∃[ N ] (Normal N × (M —↠ N))
-- normalize M with progress M
-- ... | inj₁ ⟨ M′ , M—→M′ ⟩ with normalize M′
-- ...   | ⟨ N , ⟨ NrmN , M′—↠N ⟩ ⟩ = ⟨ N , ⟨ NrmN , M —→⟨ M—→M′ ⟩ M′—↠N ⟩ ⟩
-- ... | inj₂ NrmM = ⟨ M , ⟨ NrmM , M ∎ ⟩ ⟩