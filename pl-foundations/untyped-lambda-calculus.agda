import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (ℕ; zero; suc; _<_; _≤?_; z≤n; s≤s)
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Decidable using (True; toWitness)

infix  4  _⊢_
infix  4  _∋_
infixl 5  _,_

infix  6  ƛ_
infix  6  ′_
infixl 7  _·_

-- we have just one type (untyped is uni-typed)
data Type : Set where
  ★ : Type

-- Show that Type is isomorphic to ⊤, the unit type.
infix 0 _≃_
record _≃_ (A B : Set) : Set where
  field
    to   : A → B
    from : B → A
    from∘to : ∀ (x : A) → from (to x) ≡ x
    to∘from : ∀ (y : B) → to (from y) ≡ y
open _≃_

data ⊤ : Set where

  tt :
    --
    ⊤

record Type≃⊤ : Set where
    field
        to : Type → ⊤
        from : ⊤ → Type
        from∘to : ∀ (x : Type) → from (to x) ≡ x
        to∘from : ∀ (y : ⊤) → to (from y) ≡ y


--  a context is a list of types, with the type of the most recently bound variable on the right. (we can use something here to make it affine)

data Context : Set where
  ∅   : Context
  _,_ : Context → Type → Context

-- Show that Context is isomorphic to ℕ.
record Context≃ℕ : Set where
    field
        to : Context → ℕ
        from : ℕ → Context
        from∘to : ∀ (x : Context) → from (to x) ≡ x
        to∘from : ∀ (y : ℕ) → to (from y) ≡ y


-- Intrinsically-scoped variables correspond to the lookup judgment.

data _∋_ : Context → Type → Set where

  Z : ∀ {Γ A}
     ---------
   → Γ , A ∋ A

  S_ : ∀ {Γ A B}
    → Γ ∋ A
      ---------
    → Γ , B ∋ A

-- We could write the rules with all instances of A and B replaced by ★, but arguably it is clearer not to do so.
-- Because ★ is the only type, the judgment doesn’t guarantee anything useful about types. But it does ensure that all variables are in scope. For instance, we cannot use S S Z in a context that only binds two variables.

-- Intrinsically-scoped terms correspond to the typing judgment, but with ★ as the only type. The result is that we check that terms are well scoped — that is, that all variables they mention are in scope — but not that they are well typed:

data _⊢_ : Context → Type → Set where

  `_ : ∀ {Γ A}
    → Γ ∋ A
      -----
    → Γ ⊢ A

  ƛ_  :  ∀ {Γ}
    → Γ , ★ ⊢ ★
      ---------
    → Γ ⊢ ★

  _·_ : ∀ {Γ}
    → Γ ⊢ ★
    → Γ ⊢ ★
      ------
    → Γ ⊢ ★

-- writing variables as numerals: we can convert a natural to the corresponding de bruijn index. We no longer need to lookup the etype in the context since every variable has the same type (what whe could do in affine is lookup the context to check the usage)

length : Context → ℕ
length ∅        =  zero
length (Γ , _)  =  suc (length Γ)

count : ∀ {Γ} → {n : ℕ} → (p : n < length Γ) → Γ ∋ ★
count {Γ , ★} {zero}    (s≤s z≤n)  =  Z
count {Γ , ★} {(suc n)} (s≤s p)    =  S (count p)

-- We can then introduce a convenient abbreviation for variables:

#_ : ∀ {Γ}
  → (n : ℕ)
  → {n∈Γ : True (suc n ≤? length Γ)}
    --------------------------------
  → Γ ⊢ ★
#_ n {n∈Γ}  =  ` count (toWitness n∈Γ)

-- computing two plus two on church numerals
twoᶜ : ∀ {Γ} → Γ ⊢ ★
twoᶜ = ƛ ƛ (# 1 · (# 1 · # 0))

fourᶜ : ∀ {Γ} → Γ ⊢ ★
fourᶜ = ƛ ƛ (# 1 · (# 1 · (# 1 · (# 1 · # 0))))

plusᶜ : ∀ {Γ} → Γ ⊢ ★
plusᶜ = ƛ ƛ ƛ ƛ (# 3 · # 1 · (# 2 · # 1 · # 0))

2+2ᶜ : ∅ ⊢ ★
2+2ᶜ = plusᶜ · twoᶜ · twoᶜ

-- computing one plus one on church numerals
oneᶜ : ∀ {Γ} → Γ ⊢ ★
oneᶜ = ƛ ƛ (# 1 · # 0)

1+1ᶜ : ∅ ⊢ ★
1+1ᶜ = plusᶜ · oneᶜ · oneᶜ

-- Before, reduction stopped when we reached a lambda term, so we had to compute plusᶜ · twoᶜ · twoᶜ · sucᶜ · `zero to ensure we reduced to a representation of the natural four. Now, reduction continues under lambda, so we don’t need the extra arguments. It is convenient to define a term to represent four as a Church numeral, as well as two.

-- renaming -> same as before
ext : ∀ {Γ Δ} → (∀ {A} → Γ ∋ A → Δ ∋ A)
    -----------------------------------
  → (∀ {A B} → Γ , B ∋ A → Δ , B ∋ A)
ext ρ Z      =  Z
ext ρ (S x)  =  S (ρ x)

-- Now it is straightforward to define renaming:

rename : ∀ {Γ Δ}
  → (∀ {A} → Γ ∋ A → Δ ∋ A)
    ------------------------
  → (∀ {A} → Γ ⊢ A → Δ ⊢ A)
rename ρ (` x)          =  ` (ρ x)
rename ρ (ƛ N)          =  ƛ (rename (ext ρ) N)
rename ρ (L · M)        =  (rename ρ L) · (rename ρ M)

-- Simultaneous substitution
-- Our definition of substitution is also exactly as before. First we need an extension lemma:
exts : ∀ {Γ Δ} → (∀ {A} → Γ ∋ A → Δ ⊢ A)
    ----------------------------------
  → (∀ {A B} → Γ , B ∋ A → Δ , B ⊢ A)
exts σ Z      =  ` Z
exts σ (S x)  =  rename S_ (σ x)

-- Now it is straightforward to define substitution:
subst : ∀ {Γ Δ}
  → (∀ {A} → Γ ∋ A → Δ ⊢ A)
    ------------------------
  → (∀ {A} → Γ ⊢ A → Δ ⊢ A)
subst σ (` k)          =  σ k
subst σ (ƛ N)          =  ƛ (subst (exts σ) N)
subst σ (L · M)        =  (subst σ L) · (subst σ M)

-- Single substitution
subst-zero : ∀ {Γ B} → (Γ ⊢ B) → ∀ {A} → (Γ , B ∋ A) → (Γ ⊢ A)
subst-zero M Z      =  M
subst-zero M (S x)  =  ` x

_[_] : ∀ {Γ A B}
        → Γ , B ⊢ A
        → Γ ⊢ B
          ---------
        → Γ ⊢ A
_[_] {Γ} {A} {B} N M =  subst {Γ , B} {Γ} (subst-zero M) {A} N

-- Neutral and normal terms
-- Reduction continues until a term is fully normalised. Hence, instead of values, we are now interested in normal forms. Terms in normal form are defined by mutual recursion with neutral terms:

data Neutral : ∀ {Γ A} → Γ ⊢ A → Set
data Normal  : ∀ {Γ A} → Γ ⊢ A → Set

data Neutral where

  `_  : ∀ {Γ A} (x : Γ ∋ A)
      -------------
    → Neutral (` x)

  _·_  : ∀ {Γ} {L M : Γ ⊢ ★}
    → Neutral L
    → Normal M
      ---------------
    → Neutral (L · M)

-- A term is a normal form if it is neutral or an abstraction where the body is a normal form. We use ′_ to label neutral terms. Like `_, it is unobtrusive:

data Normal where

  ′_ : ∀ {Γ A} {M : Γ ⊢ A}
    → Neutral M
      ---------
    → Normal M

  ƛ_  : ∀ {Γ} {N : Γ , ★ ⊢ ★}
    → Normal N
      ------------
    → Normal (ƛ N)


-- We introduce a convenient abbreviation for evidence that a variable is neutral:
#′_ : ∀ {Γ} (n : ℕ) {n∈Γ : True (suc n ≤? length Γ)} → Neutral {Γ} (# n)
#′_ n {n∈Γ}  =  ` count (toWitness n∈Γ)

-- For example, here is the evidence that the Church numeral two is in normal form:
_ : Normal (twoᶜ {∅})
_ = ƛ ƛ (′ #′ 1 · (′ #′ 1 · (′ #′ 0)))

-- The evidence that a term is in normal form is almost identical to the term itself, decorated with some additional primes to indicate neutral terms, and using #′ in place of #

-- Reduction step
-- The reduction rules are altered to switch from call-by-value to call-by-name and to enable full normalisation:

-- The rule ξ₁ remains the same as it was for the simply-typed lambda calculus.

-- In rule ξ₂, the requirement that the term L is a value is dropped. So this rule can overlap with ξ₁ and reduction is non-deterministic. One can choose to reduce a term inside either L or M.

-- In rule β, the requirement that the argument is a value is dropped, corresponding to call-by-name evaluation. This introduces further non-determinism, as β overlaps with ξ₂ when there are redexes in the argument.

-- A new rule ζ is added, to enable reduction underneath a lambda.

-- Here are the formalised rules:

infix 2 _—→_

data _—→_ : ∀ {Γ A} → (Γ ⊢ A) → (Γ ⊢ A) → Set where

  ξ₁ : ∀ {Γ} {L L′ M : Γ ⊢ ★}
    → L —→ L′
      ----------------
    → L · M —→ L′ · M

  ξ₂ : ∀ {Γ} {L M M′ : Γ ⊢ ★}
    → M —→ M′
      ----------------
    → L · M —→ L · M′

  β : ∀ {Γ} {N : Γ , ★ ⊢ ★} {M : Γ ⊢ ★}
      ---------------------------------
    → (ƛ N) · M —→ N [ M ]

  ζ : ∀ {Γ} {N N′ : Γ , ★ ⊢ ★}
    → N —→ N′
      -----------
    → ƛ N —→ ƛ N′


-- Reflexive and transitive closure

infix  2 _—↠_
infix  1 begin_
infixr 2 _—→⟨_⟩_
infix  3 _∎

data _—↠_ {Γ A} : (Γ ⊢ A) → (Γ ⊢ A) → Set where

  _∎ : (M : Γ ⊢ A)
      ------
    → M —↠ M

  step—→ : (L : Γ ⊢ A) {M N : Γ ⊢ A}
    → M —↠ N
    → L —→ M
      ------
    → L —↠ N

pattern _—→⟨_⟩_ L L—→M M—↠N = step—→ L M—↠N L—→M

begin_ : ∀ {Γ A} {M N : Γ ⊢ A}
  → M —↠ N
    ------
  → M —↠ N
begin M—↠N = M—↠N

-- Example reduction sequence
-- Here is the demonstration that two plus two is four:

_ : 2+2ᶜ —↠ fourᶜ
_ =
  begin
    plusᶜ · twoᶜ · twoᶜ
  —→⟨ ξ₁ β ⟩
    (ƛ ƛ ƛ twoᶜ · # 1 · (# 2 · # 1 · # 0)) · twoᶜ
  —→⟨ β ⟩
    ƛ ƛ twoᶜ · # 1 · (twoᶜ · # 1 · # 0)
  —→⟨ ζ (ζ (ξ₁ β)) ⟩
    ƛ ƛ ((ƛ # 2 · (# 2 · # 0)) · (twoᶜ · # 1 · # 0))
  —→⟨ ζ (ζ β) ⟩
    ƛ ƛ # 1 · (# 1 · (twoᶜ · # 1 · # 0))
  —→⟨ ζ (ζ (ξ₂ (ξ₂ (ξ₁ β)))) ⟩
    ƛ ƛ # 1 · (# 1 · ((ƛ # 2 · (# 2 · # 0)) · # 0))
  —→⟨ ζ (ζ (ξ₂ (ξ₂ β))) ⟩
   ƛ (ƛ # 1 · (# 1 · (# 1 · (# 1 · # 0))))
  ∎

-- After just two steps the top-level term is an abstraction, and ζ rules drive the rest of the normalisation.
-- Progress
-- Progress adapts. Instead of claiming that every term either is a value or takes a reduction step, we claim that every term is either in normal form or takes a reduction step.

-- Previously, progress only applied to closed, well-typed terms. We had to rule out terms where we apply something other than a function (such as `zero) or terms with a free variable. Now we can demonstrate it for open, well-scoped terms. The definition of normal form permits free variables, and we have no terms that are not functions.

-- A term makes progress if it can take a step or is in normal form:

data Progress {Γ A} (M : Γ ⊢ A) : Set where

  step : ∀ {N : Γ ⊢ A}
    → M —→ N
      ----------
    → Progress M

  done :
      Normal M
      ----------
    → Progress M

progress : ∀ {Γ A} → (M : Γ ⊢ A) → Progress M
progress (` x)                                 =  done (′ ` x)
progress (ƛ N)  with  progress N
... | step N—→N′                               =  step (ζ N—→N′)
... | done NrmN                                =  done (ƛ NrmN)
progress (` x · M) with progress M
... | step M—→M′                               =  step (ξ₂ M—→M′)
... | done NrmM                                =  done (′ (` x) · NrmM)
progress ((ƛ N) · M)                           =  step β
progress (L@(_ · _) · M) with progress L
... | step L—→L′                               =  step (ξ₁ L—→L′)
... | done (′ NeuL) with progress M
...    | step M—→M′                            =  step (ξ₂ M—→M′)
...    | done NrmM                             =  done (′ NeuL · NrmM)

-- We induct on the evidence that the term is well scoped:

-- If the term is a variable, then it is in normal form. (This contrasts with previous proofs, where the variable case was ruled out by the restriction to closed terms.)
-- If the term is an abstraction, recursively invoke progress on the body. (This contrast with previous proofs, where an abstraction is immediately a value.):
-- If it steps, then the whole term steps via ζ.
-- If it is in normal form, then so is the whole term.
-- If the term is an application, consider the function subterm:
-- If it is a variable, recursively invoke progress on the argument:
-- If it steps, then the whole term steps via ξ₂;
-- If it is normal, then so is the whole term.
-- If it is an abstraction, then the whole term steps via β.
-- If it is an application, recursively apply progress to the function subterm:
-- If it steps, then the whole term steps via ξ₁.
-- If it is normal, recursively apply progress to the argument subterm:
-- If it steps, then the whole term steps via ξ₂.
-- If it is normal, then so is the whole term.
-- The final equation for progress uses an at pattern of the form P@Q, which matches only if both pattern P and pattern Q match. Character @ is one of the few that Agda doesn’t allow in names, so spaces are not required around it. In this case, the pattern ensures that L is an application.

