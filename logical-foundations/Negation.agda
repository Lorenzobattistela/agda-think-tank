module logical-foundations.Negation where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Nat
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product 
open import logical-foundations.Isomorphism using (_≃_; extensionality; _∘_)

-- given A, the negation of A holds if A cannot hold. We formalise it by declaring negation to be the same as implication of false

¬_ : Set → Set
¬ A = A → ⊥
-- if assuming A leads to the conclusion ⊥ , then we must have not A (same as in FO logic)
-- evidence that ¬A holds os pf the form λ{ x → N}
-- where N is a term of ⊥ containing as a free variable x of type A. In other words, evidence that ¬ A holds is a function that converts evidence that A holds into evidence that ⊥ holds.
-- So we have the elimination rule:

¬-elim : ∀ {A : Set}
  → ¬ A
  → A
    ---
  → ⊥
¬-elim ¬x x = ¬x x
-- here we write ¬x for evidence of ¬A and x for evidence of A. this means that not x must be a function from A to ⊥. This rule is jus a special case of elimination of implication

infix 3 ¬_

-- in classical logica, A is equivalent to ¬¬A. But agda use intuitionistic logic, where we have only half of this equivalence, namely that A implies ¬¬A

¬¬-intro : ∀ {A : Set}
  → A
    ----
  → ¬ ¬ A
¬¬-intro x = λ {¬x → ¬x x}

-- or we can use:
¬¬-intro′ : ∀ {A : Set}
  → A
    ----
  → ¬ ¬ A
¬¬-intro′ x ¬x = ¬x x

-- we cannot show that not not A implies A, but we can show that not not not A implies not A

¬¬¬-elim : ∀ {A : Set}
  → ¬ ¬ ¬ A
    ------
  → ¬ A
¬¬¬-elim ¬¬¬x = λ x → ¬¬¬x (¬¬-intro x)
-- let notnotnot x be evidence of ¬ ¬ ¬ A. We will show that assuming A leads to a contradiction and hence ¬ A must hold. Let x be evidence of A. Then by the previous result, we can conclude ¬ ¬ A, evidenced by ¬¬-intro x. Then from ¬ ¬ ¬ A and ¬ ¬ A we have a contradiction, evidence by ¬¬x (¬¬-intro x)/ Hence we have shown ¬ A.
-- Another law of logic is contraposition, stating that if A implies B then ¬ B implies ¬ A

contraposition : ∀ {A B : Set}
  → (A → B)
    ------------
  → (¬ B → ¬ A)
contraposition f ¬y x = ¬y (f x)
-- let f be evidence of A→B and ¬y be evidence of ¬B. We will show that assuming A leads to a contradiction, and hence ¬ A must hold. Let x be evidence of A. Then from A → B and A we may conclude B, evidenced by f x, and from B and ¬ B we may conclude ⊥, evidenced by ¬y (f x) . Hence we have shown ¬A
-- using negation, we can define inequality

_≢_ : ∀ {A : Set} → A → A → Set
x ≢ y = ¬ (x ≡ y)

-- this is our first use of absurd pattern in a lambda expression. The type M ≡ N is occupied exactly when M and N simplify to identical terms. Since 1 and 2 simplify to distinc normal forms, Agda determines that there is no possible evidence that 1 ≡ 2. We can also validate Peanos postulate that zero is not the successor of any (nat) number.
_ : 1 ≢ 2
_ = λ()

peano : ∀ {m : ℕ} → zero ≢ suc m
peano = λ()

-- given the correspondence of implication to exponentiation and false to the type with no members, we ca view negation as raising to the zero power
-- corresponds to 0 ^ n = 1 if n = 0 and 0 if n != 0

id : ⊥ → ⊥
id x = x

id′ : ⊥ → ⊥
id′ ()

-- there is exactly one proof of ⊥ → ⊥.
-- we can write the this in the above two ways, and prove them equal with extensionality

id≡id′ : id ≡ id′ 
id≡id′ = extensionality(λ())
-- by extensionality, id ≡ id′ holds if for every x in their domain we have id x ≡ id′ x, but there is no x in their domain and therefore the equality holds trivially

assimilation : ∀ {A : Set} (¬x ¬x′ : ¬ A) → ¬x ≡ ¬x′
assimilation ¬x ¬x′ = extensionality (λ x → ⊥-elim (¬x x))
-- Evidence for ¬ A implies that any evidence of A immediately leads to a contradiction. But extensionality quantifies over all x such that A holds, hence any such x immediately leads to a contradiction, again causing the equality to hold trivially.
--
-- Exercise <-irreflexive
-- Using negation, show that strict inequality is irreflexive, that is, n < n holds for no n

-- proof by induction on N. In the base case, its impossible to construct a proof of zero < zero, so we use empty pattern
-- inductive case n = suc(n). If we have a proof of suc n < suc n, it must have been constructed using the s<=constructor, which means that we have a proof of n < n. 
<-irreflexive : ∀ (n : ℕ) → ¬ (n < n)
<-irreflexive zero ()
<-irreflexive (suc n) (s≤s n<n) = <-irreflexive n n<n

-- data Trichotomy (m n : ℕ) : Set where
--   less    : m < n → ¬ (m ≡ n) → ¬ (m > n) → Trichotomy m n
--   equal   : m ≡ n → ¬ (m < n) → ¬ (m > n) → Trichotomy m n
--   greater : m > n → ¬ (m ≡ n) → ¬ (m < n) → Trichotomy m n
-- 
-- -- Helper lemmas
-- suc-injective : ∀ {m n} → suc m ≡ suc n → m ≡ n
-- suc-injective refl = refl
-- 
-- ¬s≡z : ∀ {n} → ¬ (suc n ≡ zero)
-- ¬s≡z ()
-- 
-- -- Main trichotomy proof
-- trichotomy : ∀ m n → Trichotomy m n
-- trichotomy zero zero = equal refl (λ ()) (λ ())
-- trichotomy zero (suc n) = less z<s (λ ()) (λ ())
-- trichotomy (suc m) zero = greater z<s (λ ()) (λ ())
-- trichotomy (suc m) (suc n) with trichotomy m n
-- ... | less m<n ¬m≡n ¬m>n =
--   less (s<s m<n)
--        (λ sm≡sn → ¬m≡n (suc-injective sm≡sn))
--        (λ sn<sm → ¬m>n (λ n<m → n<m))
-- ... | equal m≡n ¬m<n ¬m>n =
--   equal (Eq.cong suc m≡n)
--         (λ sm<sn → ¬m<n (λ m<n → m<n))
--         (λ sn<sm → ¬m>n (λ n<m → n<m))
-- ... | greater m>n ¬m≡n ¬m<n =
--   greater (s<s m>n)
--           (λ sm≡sn → ¬m≡n (suc-injective sm≡sn))
--           (λ sm<sn → ¬m<n (λ m<n → m<n))
-- 


-- intuitive and classical logical
-- Intuitionists, concerned by assumptions made by some logicians about the nature of infinity, insist upon a constructionist
-- notion of truth. In particular, they insist that a proof of A ⊎ B must show chich of A or B holds
-- Intuitionists also reject the law of the excluded middle, which asserts A ⊎ ¬A for every A, since the law gives
-- no clue as to which of A or ¬ A holds. Heyting formalised a variant of Hilberts classical logic that
-- captures the intuitionistic notion of provability. In particular, the law of the excluded middle is provable
-- by hilberts, but no in heytings. 
-- Propositions as types was first formulated for intuitionistic logic. It is a perfect fit, because in the intuitionist
-- interpretation the formula A ⊎ B is provable exactly when one exhibits either a proof of A or a proof of B,
-- so the type corresponding to the disjunction is a disjoint sum
--
-- Excluded middle is irrefutable

postulate
  em : ∀ {A : Set} → A ⊎ ¬ A
-- it does not hold for intuitionistic, but we can show it is irrefutable (negation of its negation is provable)

em-irrefutable : ∀ {A : Set} → ¬ ¬ (A ⊎ ¬ A)
-- given evidence k that ¬ (A ⊎ ¬ A), that is, a function that given a value of type A ⊎ ¬ A returns a value of the empty type
-- we must fill in ? with a term that returns a value of the empty type. The only way we can get a value of the empty type
-- is by applying k itself:
-- em-irrefutable k = k ?
-- We need to fill the new hole with a value of type A ⊎ ¬ A. We dont have a value of type A to hand, so lets pick
-- the second disjunct
-- em-irrefutable k = k (inj₂ λ{x → ?})
-- the second disjunc accepts evidence of ¬ A, that is, a function that given a value of type A returns a value of the empty type
-- we bind x to the value o ftype A, and now we need to fill the hole with a value of the empty type
-- Once again, the only way we can get a value of the empty type is by applying k itself, so lets expand the hole:
-- em-irrefutable k = k (inj₂ λ{x → k ?})
-- this time we do have a value of type A to hand, namely x, so we can pick the first disjunct
em-irrefutable k = k (inj₂ (λ x → k (inj₁ x)))

Stable : Set → Set
Stable A = ¬ ¬ A → A


negatedStable : ∀ {A : Set} → Stable (¬ A)
negatedStable ¬¬¬a a = ¬¬¬a (λ ¬a → ¬a a)

stableConjunction : ∀ {A B : Set} → Stable A → Stable B → Stable (A × B)
stableConjunction stableA stableB ¬¬a×b =
  stableA (λ ¬a → ¬¬a×b (λ a×b → ¬a (proj₁ a×b))) ,
  stableB (λ ¬b → ¬¬a×b (λ a×b → ¬b (proj₂ a×b)))
































