module logical-foundations.Decidable where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Negation using () renaming (contradiction to ¬¬-intro)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import logical-foundations.Relations using (_<_; z<s; s<s)
open import logical-foundations.Isomorphism using (_⇔_)

infix 4 _≤_

data _≤_ : ℕ → ℕ → Set where

  z≤n : ∀ {n : ℕ}
      ------------
    → zero ≤ n

  s≤s : ∀ {m n : ℕ}
    → m ≤ n
      -----------
    → suc m ≤ suc n

2≤4 : 2 ≤ 4
2≤4 = s≤s (s≤s z≤n)

-- the occurrence of () attests to the fact that there is no possible evidence for 2 <= 0, which z<=n cannot
-- match (because 2 is not zero) and s<=s cannot match (because 0 cannot match suc n)
¬4≤2 : ¬ (4 ≤ 2)
¬4≤2 (s≤s (s≤s ()))

-- an alternative which may seem more familiar is to define a type for booleans
data Bool : Set where
  true : Bool
  false : Bool

-- given booleans, we can define a function of two numbers that computes to true if the comparison holds and false otherwise

infix 4 _≤ᵇ_

_≤ᵇ_ : ℕ → ℕ → Bool
zero ≤ᵇ n      = true
suc m ≤ᵇ zero  = false
suc m ≤ᵇ suc n = m ≤ᵇ n

-- the first and last clauses of this def resemble the two constructors of the corresponding inductive
-- datatype, while the middle clause arises because there is no possible evidence that suc m <= zero for any m
-- For example, we can compute that 2 <=b 4 holds

_ : (2 ≤ᵇ 4) ≡ true
_ =
  begin
    2 ≤ᵇ 4
  ≡⟨⟩
    1 ≤ᵇ 3
  ≡⟨⟩
    0 ≤ᵇ 2
  ≡⟨⟩
    true
  ∎

_ : (4 ≤ᵇ 2) ≡ false
_ =
  begin
    4 ≤ᵇ 2
  ≡⟨⟩
    3 ≤ᵇ 1
  ≡⟨⟩
    2 ≤ᵇ 0
  ≡⟨⟩
    false
  ∎
-- in the first case, it takes two steps to reduce the first argument to zero, and one more step to compute true, corresponding
-- to the two uses of s<=s and the one use of z<=n when providing evidence that 2 <= 4. In the second case, it takes two steps 
-- to reduce the second argument to zero and one more step to compute false, corresponding to the two uses of s<=s and the one use
-- of () when showing there can be no evidence that 4 <= 2

-- Relating Evidence and Computation
-- We would hope to be able to show these two approaches are related, and indeed we can. First, we define a function
-- that lets us map from the computation world to the evidence world

T : Bool → Set
T true = T
T false = ⊥

-- recall that ⊤ is the unit type which contains the single element tt, and the ⊥ is the empty type which
-- contains no values. If b is of type Bool, then tt provides evidence that T b holds if b true, while there is no possible
-- evidence that T b holds if b is false
-- Another way to put this is that T b is inhabited exactly when b ≡ true is inhabited. In the forward direction, we need to do a
-- case analysis on the boolean b

T→≡ : ∀ (b : Bool) → T b → b ≡ true
T→≡ true tt = refl
T→≡ false ()
-- if b is true then T b is inhabited by tt and b ≡ true is inhabited by refl, while if b is false then T b is uninhabite
-- If the reverse direction, there is no need for a case analysis on the boolean b
≡→T : ∀ {b : Bool} → b ≡ true → T b
≡→T refl = tt
-- if b ≡ true is inhabited by refl we know that b is true and hence T b is inhabited by tt
-- now we chan show that T (m <=b n) is inhabited exactly when m <= n is inhabited
-- in the forward direction, we consider the three clauses in the defintion of <=b




























