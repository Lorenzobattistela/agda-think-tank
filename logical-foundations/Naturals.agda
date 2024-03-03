{-# OPTIONS --without-K #-}

module logical-foundations.Naturals where

data ℕ : Set where
  zero : ℕ
  suc : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _∎)

seven : ℕ
seven = suc(suc(suc(suc(suc(suc(suc(0)))))))

_+_ : ℕ → ℕ → ℕ
zero + n = n 
(suc m) + n = suc(m + n)

-- sufficient proof
_ : 2 + 3 ≡ 5
_ = refl

_ : 2 + 3 ≡ 5
_ =
  begin
    2 + 3
  ≡⟨⟩    -- is shorthand for
    (suc (suc zero)) + (suc (suc (suc zero)))
  ≡⟨⟩    -- inductive case
    suc ((suc zero) + (suc (suc (suc zero))))
  ≡⟨⟩    -- inductive case
    suc (suc (zero + (suc (suc (suc zero)))))
  ≡⟨⟩    -- base case
    suc (suc (suc (suc (suc zero))))
  ≡⟨⟩    -- is longhand for
    5
  ∎

_ : 2 + 3 ≡ 5
_ =
  begin
    2 + 3
  ≡⟨⟩
    suc (1 + 3)
  ≡⟨⟩
    suc (suc (0 + 3))
  ≡⟨⟩
    suc (suc 3)
  ≡⟨⟩
    5
  ∎

-- * exercise: compute 3 * 4 writing out reasoning and chain of equations using notations for *
_*_ : ℕ → ℕ → ℕ
zero * n = zero
(suc m) * n = n + (m * n)

_ =
  begin
    3 * 4
    ≡⟨⟩ -- inductive case
    4 + (2 * 4)
    ≡⟨⟩ -- inductive case
    4 + (4 + (1 * 4))
    ≡⟨⟩ -- inductive case
    4 + (4 + (4 + (0 * 4)))
    ≡⟨⟩ -- base case
    4 + (4 + (4 + (0)))
    ≡⟨⟩
    12
 ∎

_^_ : ℕ → ℕ → ℕ
m ^ zero = 1
m ^ (suc n) = m * (m ^ n)

_ =
  begin
    3 ^ 4
    ≡⟨⟩ -- inductive
    3 * (3 ^ 3)
    ≡⟨⟩
    3 * (3 * (3 ^ 2))
    ≡⟨⟩
    3 * (3 * (3 * (3 ^ 1)))
    ≡⟨⟩
    3 * (3 * (3 * (3 * (3 ^ 0))))
    ≡⟨⟩
    3 * (3 * (3 * (3 * 1)))
    ≡⟨⟩
    81
  ∎


_∸_ : ℕ → ℕ → ℕ
m     ∸ zero   =  m
zero  ∸ suc n  =  zero
suc m ∸ suc n  =  m ∸ n

-- computing 5 ∸ 3 and 3 ∸ 5
_ =
  begin
    5 ∸ 3
  ≡⟨⟩
    4 ∸ 2
  ≡⟨⟩
    3 ∸ 1
  ≡⟨⟩
    2 ∸ 0
  ≡⟨⟩
    2
  ∎

_ =
  begin
    3 ∸ 5
  ≡⟨⟩
    2 ∸ 4
  ≡⟨⟩
    1 ∸ 3
  ≡⟨⟩
    0 ∸ 3
  ≡⟨⟩
    0 ∸ 2
  ≡⟨⟩
    0 ∸ 1
  ≡⟨⟩
    0 ∸ 0
  ≡⟨⟩
  0
  ∎

infixl 6  _+_  _∸_
infixl 7  _*_

{-# BUILTIN NATPLUS _+_ #-}
{-# BUILTIN NATTIMES _*_ #-}
{-# BUILTIN NATMINUS _∸_ #-}

-- Exercise: Bin

data Bin : Set where
  ⟨⟩ : Bin
  _O : Bin → Bin
  _I : Bin → Bin

inc : Bin → Bin
inc ⟨⟩ = ⟨⟩ I
inc (_O n) = _I n
inc (_I n) = _O (inc n)

_ : inc (⟨⟩ I O I I) ≡ ⟨⟩ I I O O
_ = refl

_ : inc (⟨⟩ I I I I) ≡ ⟨⟩ I O O O O
_ = refl

to : ℕ → Bin
to zero = ⟨⟩
to (suc x) = inc (to x)

_ =
  begin
    to 3
  ≡⟨⟩
    inc (to 2)
  ≡⟨⟩
    inc (inc (to 1))
  ≡⟨⟩
    inc (inc (inc (to 0)))
  ≡⟨⟩
    inc (inc (inc ⟨⟩))
  ≡⟨⟩
    inc (inc (⟨⟩ I))
  ≡⟨⟩
    inc (⟨⟩ I O)
  ≡⟨⟩
    ⟨⟩ I I
  ∎

_ : to zero ≡ ⟨⟩
_ = refl

_ : to 3 ≡ ⟨⟩ I I
_ = refl

from : Bin → ℕ
from ⟨⟩ = zero
from (x O) = 2 * from(x)
from (x I) = 2 * from(x) + 1

_ : from ⟨⟩ ≡ zero
_ = refl

_ : from (⟨⟩ O I) ≡ 1
_ = refl

_ : from (⟨⟩ I O) ≡ 2
_ = refl
