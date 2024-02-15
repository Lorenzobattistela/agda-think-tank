import Data.Nat using (zero; suc; _+_; _*_; _^_; _∸_)
open import Data.Nat
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning using (begin_; _∎)

seven : ℕ
seven = suc(suc(suc(suc(suc(suc(suc(0)))))))

-- sufficient proof
_ : 2 + 3 ≡ 5
_ = refl

expo : ℕ → ℕ → ℕ
expo m zero = 1
expo m (suc n) = m * (expo m n)


