import Data.Nat using (zero; suc; _+_; _*_; _^_; _∸_)
open import Data.Nat
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl;)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _∎)

seven : ℕ
seven = suc(suc(suc(suc(suc(suc(suc(0)))))))

-- sufficient proof
_ : 2 + 3 ≡ 5
_ = refl

-- * exercise: compute 3 * 4 writing out reasoning and chain of equations using notations for *

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

expo : ℕ → ℕ → ℕ
expo m zero = 1
expo m (suc n) = m * (expo m n)


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