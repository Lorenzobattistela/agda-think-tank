module logical-foundations.Negation where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Nat using (ℕ; zero; suc; _<_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_)
open import logical-foundations.Isomorphism using (_≃_; extensionality)

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

-- <-irreflexive : ∀ (n : ℕ) → ¬ (n < n)
-- <-irreflexive zero ()
-- <-irreflexive (suc n) (s<s n<n) = <-irreflexive n n<n

















































