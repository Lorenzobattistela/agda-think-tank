import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; step-≡; _∎)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_;_^_)

-- proving associativity
-- here we define the identifier +- assoc which rpovides evidences for its following proposition

_ : (3 + 4) + 5 ≡ 3 + (4 + 5)
_ =
  begin
    (3 + 4) + 5
  step-≡
    7 + 5
  step-≡
    12
  step-≡
    3 + 9
  step-≡
    3 + (4 + 5)
  ∎