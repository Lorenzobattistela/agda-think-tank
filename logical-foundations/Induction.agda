module logical-foundations.Induction where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_;_^_)

-- associativity:

_ : (3 + 4) + 5 ≡ 3 + (4 + 5)
_ =
  begin
    (3 + 4) + 5
  ≡⟨⟩
    (7 + 5)
  ≡⟨⟩
    12
  ≡⟨⟩
    3 + 9
  ≡⟨⟩
    3 + (4 + 5)
  ∎

-- proof of associativity by induction

-- proofs by induction need to proof the base case and the inductive case. For example, for nats, we need to proof (base case) that the property holds for zero, and then (inductive) we assume the prop holds for an arbitrary bat m and we show it must hold for suc .

-- -------
--  P zero

--  P m
-- -----------
--  P (suc m)

-- proof that (m + n) + p ≡ m + (n + p)

-- ----------------------------------
--  (zero + n) + p ≡ zero + (n + p)

-- (m + n) + p ≡ m + (n + p)
-- ---------------------------------
-- (suc m + n) + p ≡ suc m + (n + p)


-- returns evidence for the corresponding instance of equation (receiving 3 nats that bind to m n and p)
+-assoc : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
-- base case holds trivially (n + p ≡ n + p)
+-assoc zero n p =
    begin
        (zero + n) + p 
    ≡⟨⟩
        n + p 
    ∎

-- a relation is said to be a congruence for a fn if it preserves by applying that function. If e is evidence that x ≡ y, then cong f e is evidence that f x ≡  f y for any f.
-- That said, we use conf suc to show that f x ≡ f y for any x and y and suc if x ≡ y.
+-assoc (suc m) n p =
    begin
        (suc m + n) + p 
    ≡⟨⟩
        suc(m + n) + p 
    ≡⟨⟩
        suc((m + n) + p)
    -- we recursively invocate the assoc function defined. We proof associativity of larger numbers in terms of associativity of smaller numbers.
    ≡⟨ cong suc (+-assoc m n p)⟩ 
        suc (m + (n + p))
    ≡⟨⟩
        suc m + (n + p)
    ∎

-- induction as recursion: concrete example of computation
+-assoc-0 : ∀ (n p : ℕ) → (0 + n) + p ≡ 0 + (n + p)
+-assoc-0 n p =
  begin
    (0 + n) + p
  ≡⟨⟩
    n + p
  ≡⟨⟩
    0 + (n + p)
  ∎

+-assoc-1 : ∀ (n p : ℕ) → (1 + n) + p ≡ 1 + (n + p)
+-assoc-1 n p =
  begin
    (1 + n) + p
  ≡⟨⟩
    suc (0 + n) + p
  ≡⟨⟩
    suc ((0 + n) + p)
  ≡⟨ cong suc (+-assoc-0 n p) ⟩
    suc (0 + (n + p))
  ≡⟨⟩
    1 + (n + p)
  ∎

+-assoc-2 : ∀ (n p : ℕ) → (2 + n) + p ≡ 2 + (n + p)
+-assoc-2 n p =
  begin
    (2 + n) + p
  ≡⟨⟩
    suc (1 + n) + p
  ≡⟨⟩
    suc ((1 + n) + p)
  ≡⟨ cong suc (+-assoc-1 n p) ⟩
    suc (1 + (n + p))
  ≡⟨⟩
    2 + (n + p)
  ∎

-- Univ quantifiers are used to associated variables are associated with each argument type, and the result type may mention (or depend upon) these variables; hence they are called dependent functions.

-- Ordinary functions are just a special case of dependent functions. The signatures:
-- _+_ : ℕ → ℕ → ℕ
-- _+_ : ∀ (m n : ℕ) → ℕ
-- _+_ : ∀ (m : ℕ) → ∀ (n : ℕ) → ℕ
-- are all the same

-- proving commutativity
-- m + n ≡ n + m

-- base case: zero + n ≡ n and m + zero ≡ m

+-identityʳ : ∀ (m : ℕ) → m + zero ≡ m 
+-identityʳ zero =
     begin
        zero + zero
      ≡⟨⟩
        zero
      ∎
+-identityʳ (suc m) =
    begin
        suc m + zero
    ≡⟨⟩
        suc (m + zero)
    ≡⟨ cong suc (+-identityʳ m) ⟩
        suc m
    ∎