module logical-foundations.Isomorphism where

-- we introduce isomorphism as a way of asserting that two types are equal, and embedding as a way of asserting that one type is smaller than another. We apply isomorphisms in the next chapter to demonstrate that operations on types such as product and sum satisfy properties akind to associativity, commutativity and distributivity

-- ISOMORPHISM: asserting that two types are equal 
-- EMBEDDING: asserting that one type is smaller than another


import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; cong-app)
open Eq.≡-Reasoning
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-comm)

-- function composition
_∘_ : ∀ {A B C : Set} → (B → C) → (A → B) → (A → C)
(g ∘ f) x  = g (f x)

-- this is a definition that exploits lambda expressions
_∘′_ : ∀ {A B C : Set} → (B → C) → (A → B) → (A → C)
g ∘′ f  =  λ x → g (f x)

-- Extensionality
-- Asserts that the only way to distinguis functions is by applying them. If two functions applied to the same argument always yield the same result, then they are the same function. It is the converse of cong-app.

-- Agda does not presume extensionality, but we can postulate that it holds:
postulate
    extensionality : ∀ {A B : Set} {f g : A → B}
        → (∀ (x : A) → f x ≡ g x)
          ------------------------- 
        → f ≡ g 

-- postulating this does not lead to difficulties, as it is known to be consistent with the theory that underlies agda. As an example, consider that we need results from two libs, one where addition is defined as in Nats, and one where it is defined the other way around.
_+′_ : ℕ → ℕ → ℕ
m +′ zero  = m
m +′ suc n = suc (m +′ n)

-- applying commutativity, it is easy to show that both operators always return the same result given the same arguments:
same-app : ∀ (m n : ℕ) → m +′ n ≡ m + n
same-app m n rewrite +-comm m n = helper m n
  where
  helper : ∀ (m n : ℕ) → m +′ n ≡ n + m
  helper m zero    = refl
  helper m (suc n) = cong suc (helper m n)

-- however, it might be convenient to assert that the two operators are actually indistinguishable. This we can do via two applications of extensionality:
same : _+′_ ≡ _+_
same = extensionality (λ m → extensionality (λ n → same-app m n))

-- we occasionally need to postulate extensionality in what follows. More generally, we may wish to postulate extensionality for dependent functions:
postulate
    ∀-extensionality : ∀ {A : Set} {B : A → Set} {f g : ∀(x : A) → B x}
        → (∀ (x : A) → f x ≡ g x)
          -------------------------- 
        → f ≡ g 
-- and here the type of f and g has changed from A → B to ∀ (x : A) → B x, generalising ordinary functions to dependent functions.

-- Isomorphism
-- two sets are isomorphic if they are in one-to-one correspondence. Here is a formal definition of isomorphism:
infix 0 _≃_
record _≃_ (A B : Set) : Set where
    field 
        to : A → B 
        from : B → A 
        from∘to : ∀ (x : A) → from (to x) ≡ x 
        to∘from : ∀ (y : B) → to (from y) ≡ y 
open _≃_
-- lets unpack the def. An isomorphism between sets A and B consists of four things:
-- 1. A function to from A to B
-- 2. A function from B back to A
-- 3. Evience from∘to asserting that from is a left-inverse for to
-- 4. Evidence to∘from asserting that from is a right-inverse for to.
-- Particularly, the third asserts that from ∘ to is the identity and the fourth that to ∘ from is the identity, hence the names. The declaration open _≃_ makes available the names to, from, from∘to and to∘from, otherwise we would need to write _≃_.to and so on.
-- This is our first use of records. A record declaration behaves similar to a single-constructor data declaration (there are minor differences, which we discuss in Connectives.):

data _≃′_ (A B : Set): Set where
  mk-≃′ : ∀ (to : A → B) →
          ∀ (from : B → A) →
          ∀ (from∘to : (∀ (x : A) → from (to x) ≡ x)) →
          ∀ (to∘from : (∀ (y : B) → to (from y) ≡ y)) →
          A ≃′ B

to′ : ∀ {A B : Set} → (A ≃′ B) → (A → B)
to′ (mk-≃′ f g g∘f f∘g) = f

from′ : ∀ {A B : Set} → (A ≃′ B) → (B → A)
from′ (mk-≃′ f g g∘f f∘g) = g

from∘to′ : ∀ {A B : Set} → (A≃B : A ≃′ B) → (∀ (x : A) → from′ A≃B (to′ A≃B x) ≡ x)
from∘to′ (mk-≃′ f g g∘f f∘g) = g∘f

to∘from′ : ∀ {A B : Set} → (A≃B : A ≃′ B) → (∀ (y : B) → to′ A≃B (from′ A≃B y) ≡ y)
to∘from′ (mk-≃′ f g g∘f f∘g) = f∘g

-- we construct values of the record type with the syntax
-- record
--   { to    = f
--   ; from  = g
--   ; from∘to = g∘f
--   ; to∘from = f∘g
--   }
-- which corresponds to using the constructor of the corresponding inductive type
-- mk-≃′ f g g∘f f∘g
-- where f, g, g∘f, and f∘g are values of suitable types.

-- isomorphism is an equivalence
-- isomoprhism is reflexive, symmetric and transitive.
≃-refl : ∀ {A : Set}
    -----
  → A ≃ A
≃-refl =
  record
    { to      = λ{x → x}
    ; from    = λ{y → y}
    ; from∘to = λ{x → refl}
    ; to∘from = λ{y → refl}
    }

-- in the above, to and from are both bound to identity function, and∘to and to∘from are both bound to functions that discard their argument and return refl. In this case, refl alone is an adequate proof since for the left inverse, from (to x) simplifies to x and similarly for the right inverse.
-- to show isomorphism is symmetric, we simply swap the roles of to and from, and from∘to and to∘from:

≃-sym : ∀ {A B : Set}
  → A ≃ B 
    -------- 
  → B ≃ A 

≃-sym A≃B =
  record
    { to      = from A≃B
    ; from    = to   A≃B
    ; from∘to = to∘from A≃B
    ; to∘from = from∘to A≃B
    }

-- to show isomorphism is transitive, we compose the to and frmo function, and use equational reasoning to combine the inverses

≃-trans : ∀ {A B C : Set}
  → A ≃ B
  → B ≃ C
    -----
  → A ≃ C
≃-trans A≃B B≃C =
  record
    { to       = to   B≃C ∘ to   A≃B
    ; from     = from A≃B ∘ from B≃C
    ; from∘to  = λ{x →
        begin
          (from A≃B ∘ from B≃C) ((to B≃C ∘ to A≃B) x)
        ≡⟨⟩
          from A≃B (from B≃C (to B≃C (to A≃B x)))
        ≡⟨ cong (from A≃B) (from∘to B≃C (to A≃B x)) ⟩
          from A≃B (to A≃B x)
        ≡⟨ from∘to A≃B x ⟩
          x
        ∎}
    ; to∘from = λ{y →
        begin
          (to B≃C ∘ to A≃B) ((from A≃B ∘ from B≃C) y)
        ≡⟨⟩
          to B≃C (to A≃B (from A≃B (from B≃C y)))
        ≡⟨ cong (to B≃C) (to∘from A≃B (from B≃C y)) ⟩
          to B≃C (from B≃C y)
        ≡⟨ to∘from B≃C y ⟩
          y
        ∎}
    }
-- equational reasoning for isomorphism
-- it is straightforward to support a variant of equational reasoning for isomorphism. We essentially copy the previous definition of equality for isomorphism. We comit the form that corresponds to _≡⟨⟩_ , since trivial isomorphisms arise far less often than trivial equalities.

module ≃-Reasoning where

  infix  1 ≃-begin_
  infixr 2 _≃⟨_⟩_
  infix  3 _≃-∎

  ≃-begin_ : ∀ {A B : Set}
    → A ≃ B
      -----
    → A ≃ B
  ≃-begin A≃B = A≃B

  _≃⟨_⟩_ : ∀ (A : Set) {B C : Set}
    → A ≃ B
    → B ≃ C
      -----
    → A ≃ C
  A ≃⟨ A≃B ⟩ B≃C = ≃-trans A≃B B≃C

  _≃-∎ : ∀ (A : Set)
      -----
    → A ≃ A
  A ≃-∎ = ≃-refl

open ≃-Reasoning

-- embedding
-- it is a weakening of isomorphism. While an isomorphism shows that two types are in one-to-one correspondence, an embedding shows that the first type is included in the second. Or, equivalently, that there is a many-to-one correspondence between the second type and the first.

-- the formal definition of embedding:
infix 0 _≲_
record _≲_ (A B : Set) : Set where
  field
    to      : A → B
    from    : B → A
    from∘to : ∀ (x : A) → from (to x) ≡ x
open _≲_

-- it is the same as an isomoprhism, save that it lacks the to∘from field. Hence, we know that from is left-inverse to to, but not that from is right-inverse to to.
-- embedding is reflexive and transitive, but not symmetric. The proofs are cut down versions of the similar proofs for isomorphism
≲-refl : ∀ {A : Set} → A ≲ A
≲-refl =
  record
    { to      = λ{x → x}
    ; from    = λ{y → y}
    ; from∘to = λ{x → refl}
    }

≲-trans : ∀ {A B C : Set} → A ≲ B → B ≲ C → A ≲ C
≲-trans A≲B B≲C =
  record
    { to      = λ{x → to   B≲C (to   A≲B x)}
    ; from    = λ{y → from A≲B (from B≲C y)}
    ; from∘to = λ{x →
        begin
          from A≲B (from B≲C (to B≲C (to A≲B x)))
        ≡⟨ cong (from A≲B) (from∘to B≲C (to A≲B x)) ⟩
          from A≲B (to A≲B x)
        ≡⟨ from∘to A≲B x ⟩
          x
        ∎}
     }

-- it is also easy to see that if two types embed in each other, and the embedding functions correspond, then they are isomorphic. This is a weak form of anti-symmetry:

≲-antisym : ∀ {A B : Set}
  → (A≲B : A ≲ B)
  → (B≲A : B ≲ A)
  → (to A≲B ≡ from B≲A)
  → (from A≲B ≡ to B≲A)
    -------------------
  → A ≃ B
≲-antisym A≲B B≲A to≡from from≡to =
  record
    { to      = to A≲B
    ; from    = from A≲B
    ; from∘to = from∘to A≲B
    ; to∘from = λ{y →
        begin
          to A≲B (from A≲B y)
        ≡⟨ cong (to A≲B) (cong-app from≡to y) ⟩
          to A≲B (to B≲A y)
        ≡⟨ cong-app to≡from (to B≲A y) ⟩
          from B≲A (to B≲A y)
        ≡⟨ from∘to B≲A y ⟩
          y
        ∎}
    }

-- the first three components are copied from the embedding, while the last one combines the left inverse of B≲A with the equivalences of the to and from components frmo the two embeddings to obtain the right inverse of the isomorphism.

-- Equational reasoning for embedding
-- we can also support tabular reasoning for embedding, analogous to that used for isomorphism

module ≲-Reasoning where

  infix  1 ≲-begin_
  infixr 2 _≲⟨_⟩_
  infix  3 _≲-∎

  ≲-begin_ : ∀ {A B : Set}
    → A ≲ B
      -----
    → A ≲ B
  ≲-begin A≲B = A≲B

  _≲⟨_⟩_ : ∀ (A : Set) {B C : Set}
    → A ≲ B
    → B ≲ C
      -----
    → A ≲ C
  A ≲⟨ A≲B ⟩ B≲C = ≲-trans A≲B B≲C

  _≲-∎ : ∀ (A : Set)
      -----
    → A ≲ A
  A ≲-∎ = ≲-refl

open ≲-Reasoning

-- Exercise ≃-implies-≲ 
-- show that every isomorphism implies an embedding
-- postulate
--   ≃-implies-≲ : ∀ {A B : Set}
--     → A ≃ B
--       -----
--     → A ≲ B

-- -- Your code goes here


-- Exercise _⇔_ (practice)
-- Define equivalence of propositions (also known as “if and only if”) as follows:

-- record _⇔_ (A B : Set) : Set where
--   field
--     to   : A → B
--     from : B → A

-- Show that equivalence is reflexive, symmetric, and transitive.

-- Your code goes here

-- Exercise Bin-embedding (stretch)

-- Recall that Exercises Bin and Bin-laws define a datatype Bin of bitstrings representing natural numbers, and asks you to define the following functions and predicates:

-- to : ℕ → Bin
-- from : Bin → ℕ

-- which satisfy the following property:

-- from (to n) ≡ n

-- Using the above, establish that there is an embedding of ℕ into Bin.

-- Your code goes here

