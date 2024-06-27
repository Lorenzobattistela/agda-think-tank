module logical-foundations.Universals where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Relation.Nullary using (¬_)
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import logical-foundations.Isomorphism using (_≃_; extensionality; ∀-extensionality)
open import Function using (_∘_)

-- we formalise universal quantification using the dependent function type, which has appeared throughout the book
-- for example, in: +-assoc : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
-- it is a dependent function, which given values for m, n, p returns evidence for the corresponding equation

-- In general, given a variable x of type A and a proposition B x which contains x as a free variable, the universally quantified proposition ∀ (x : A) → B x holds if for every term M of type A the proposition B M holds. Here B M stands for the proposition B x with each free occurrence of x replaced by M. Variable x appears free in B x but bound in ∀ (x : A) → B x.

-- Evidence that ∀ (x : A) → B x holds is of the form

-- λ (x : A) → N x
-- where N x is a term of type B x, and N x and B x both contain a free variable x of type A. Given a term L providing evidence that ∀ (x : A) → B x holds, and a term M of type A, the term L M provides evidence that B M holds. In other words, evidence that ∀ (x : A) → B x holds is a function that converts a term M of type A into evidence that B M holds.

-- Put another way, if we know that ∀ (x : A) → B x holds and that M is a term of type A then we may conclude that B M holds:
∀-elim : ∀ {A : Set} {B : A → Set}
  → (L : ∀ (x : A) → B x) 
  → (M : A)
  → B M
∀-elim L M = L M

-- functions arise as a special case of dependent functions, where the range does not depend on a variable drawn from the domain. When a function is viewed as evidence of implication, both its argument and result are viewed as evidence, whereas when a dependent function
-- is viewed as evidence of a universal, its argument is viewed as an element of a data type and its reuslt is viewed
-- as evidence of a proposition that depends on the argument.
-- Dependent function types are sometimes referred to as dependent products.

-- show that universals distribute over conjunction:
-- postulate
  -- ∀-distrib-× : ∀ {A : Set} {B C : A → Set} →
    --(∀ (x : A) → B x × C x) ≃ (∀ (x : A) → B x) × (∀ (x : A) → C x)


-- Existentials
-- Given a variable x of type A and a proposition B x which contains x as a free variable, the existentially quantified
-- proposition ∑[ x ∈ A ] B x holds if for some term M of type A the proposition B M holds. Here B M stands for the proposition
-- B x but bound in ∑ [ x ∈ A ] B x

data ∑ (A : Set) (B : A → Set) : Set where
  ⟨_,_⟩ : (x : A) → B x → ∑ A B

∑-syntax = ∑
infix 2 ∑-syntax
-- this is our first use of a syntax declaration, specifying that the term on the left may be written with the syntax on the right
-- evidence that ∑[ x ∈ A] B x holds is of the form ⟨ M , N ⟩ where M is a term of type A, and N is evidence that B M holds
syntax ∑-syntax A (λ x → Bx) = ∑ [ x ∈ A ] Bx

-- also possible to declare using record types
record ∑′ (A : Set) (B : A → Set) : Set where
  field
    proj₁′ : A
    proj₂′ : B proj₁′ 

-- products arise as a special case of existentials, where the second component does not depend on a variable drawn from the first 
-- component. When a product is viewed as evidence of a conjunction, both of its components are viewed as evidence, whereas when
-- it is viewed as evidence of an existential, the first component is viewed as an element of a datatype and the second component
-- is viewed as evidence of a proposition that depends on the first component. 

∃ : ∀ {A : Set} (B : A → Set) → Set
∃ {A} B = ∑ A B

∃-syntax = ∃
syntax ∃-syntax (λ x → B) = ∃[ x ] B

-- if we know that vor every x of type A that B x implies C, and we know for some x of type A that B x holds, then we
-- may conclude that C holds.
∃-elim : ∀ {A : Set} {B : A → Set} {C : Set}
  → (∀ x → B x → C)
  → ∃[ x ] B x
    ----------------
  → C
∃-elim f ⟨ x , y ⟩ = f x y

-- the converse also holds and the two together form an isomorphism
∀∃-currying : ∀ {A : Set} {B : A → Set} {C : Set}
  → (∀ x → B x → C) ≃ (∃[ x ] B x → C)
∀∃-currying =
  record
    { to        = λ{ f → λ{ ⟨ x , y ⟩ → f x y }}
    ; from      = λ{ g → λ{ x → λ{ y → g ⟨ x , y ⟩ }}}
    ; from∘to   = λ{ f → refl }
    ; to∘from   = λ{ g → extensionality λ{ ⟨ x , y ⟩ → refl }}
    }


-- an existential example
-- definitions of even and odd from Relations:
data even : ℕ → Set
data odd  : ℕ → Set

data even where

  even-zero : even zero

  even-suc : ∀ {n : ℕ}
    → odd n
      ------------
    → even (suc n)

data odd where
  odd-suc : ∀ {n : ℕ}
    → even n
      -----------
    → odd (suc n)

-- we will show that even n iff ∃[ m ] (m * 2 ≡ n) and odd for 1 + m * 2 ≡ 1
even-∃ : ∀ {n : ℕ} → even n → ∃[ m ] (  m * 2 ≡ n)
odd-∃ : ∀ {n : ℕ} → odd n → ∃[ m ] (1 + m * 2 ≡ n)

even-∃ even-zero                     = ⟨ zero , refl ⟩
even-∃ (even-suc o) with odd-∃ o
...                   | ⟨ m , refl ⟩ = ⟨ suc m , refl ⟩

odd-∃ (odd-suc e)   with even-∃ e
...                   | ⟨ m , refl ⟩ = ⟨ m , refl ⟩ 
-- by defining two mutually recursive functions. Given evidence that n is even or odd, we return a number m and evidence that m * 2 = n or 1 + m * 2 = n. We induct over the evidence that n is even or odd.
-- if the number is even because it is zero, we return a pair consisting of zero and the evidence that twice zero is zero
-- if the number is even cause it is one more than an odd number, we apply induction hypothesis to give a number m and evidence that 1 + m * 2 = n. We return a pair consisting of suc m and evidence that suc m * 2 = suc , which is immediate after substituting for n
-- if the number is odd cause its succ of even, we apply induction hypothesis to give a number m and evidence that m * 2 = n. We return a pair consisting of m and evidence that 1 + m * 2 = suc n

-- the proof in the reverse direction:
∃-even : ∀ {n : ℕ} → ∃[ m ] (    m * 2 ≡ n) → even n
∃-odd  : ∀ {n : ℕ} → ∃[ m ] (1 + m * 2 ≡ n) →  odd n

∃-even ⟨  zero , refl ⟩  =  even-zero
∃-even ⟨ suc m , refl ⟩  =  even-suc (∃-odd ⟨ m , refl ⟩)

∃-odd  ⟨     m , refl ⟩  =  odd-suc (∃-even ⟨ m , refl ⟩)

-- existentials- universals and negation
-- Negation of an existential is isomorphic to the universal of a negation. Considering that existentials are generalised disjunction
-- and universals are generalised conjunction, this result is analogous to the one which tells us that negation of a disjunction is isomorphic to a conjunction of negations:
¬∃≡∀¬ : ∀ {A : Set} {B : A → Set}
  → (¬ ∃[ x ] B x) ≃ ∀ x → ¬ B x
¬∃≡∀¬ =
  record
    { to      = λ{ ¬∃xy x y → ¬∃xy ⟨ x , y ⟩ }
    ; from    = λ{ ∀¬xy ⟨ x , y ⟩ → ∀¬xy x y }
    ; from∘to = λ{ ¬∃xy → extensionality λ{ ⟨ x , y ⟩ → refl } }
    ; to∘from = λ{ ∀¬xy → refl }
    }
-- In the to direction, we are given a value ¬∃xy of type ¬ ∃[ x ] B x, and need to show that given a value x that ¬ B x follows, in other words, from a value y of type B x we can derive false. Combining x and y gives us a value ⟨ x , y ⟩ of type ∃[ x ] B x, and applying ¬∃xy to that yields a contradiction.
-- In the from direction, we are given a value ∀¬xy of type ∀ x → ¬ B x, and need to show that from a value ⟨ x , y ⟩ of type ∃[ x ] B x we can derive false. Applying ∀¬xy to x gives a value of type ¬ B x, and applying that to y yields a contradiction.
-- The two inverse proofs are straightforward, where one direction requires extensionality.




















