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
T true   =  ⊤
T false  =  ⊥

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

≤ᵇ→≤ : ∀ (m n : ℕ) → T (m ≤ᵇ n) → m ≤ n
≤ᵇ→≤ zero   n   tt = z≤n
≤ᵇ→≤ (suc m) zero  ()
≤ᵇ→≤ (suc m) (suc n) t = s≤s (≤ᵇ→≤ m n t)
-- in the first clause we have that zero <=b n is true, so T (m <=b n) is evidenced by tt, and correspondingly m <=n is evidenced by z<=n.
-- in the middle clause, we immediately have that suc m <=b zero is false, and hence T (m <=b n) is empty, so we need not provide evidence that m<=n , which is just as well since there is no such evidence,
-- In the last clause, we have that suc M <=b suc n recurses to m <=b n. We let t be the evidence of T (suc m<=b suc n) if it exists, which by definition of _<=b_ will also be evidence of T (m <=b n). We recursively invoke the function to get evidence that m <= n, which s<=s converts to evidence that suc m <= suc n

-- in the reverse dir, we consider the possible forms of evidence that m ≤ n:
≤→≤ᵇ : ∀ {m n : ℕ} → m ≤ n → T (m ≤ᵇ n)
≤→≤ᵇ z≤n  = tt
≤→≤ᵇ (s≤s m≤n)  = ≤→≤ᵇ m≤n
-- if the evidence is z<=n then we immediately have that zero <=b n is true, so T)m <=b n) is evidenced by tt. If the evidence is s<=s applied to m<=n, then suc m <=b suc n reduces to m <=b n, and we may recursively invoke the function to produce evidence that T (m<=b n)

-- The Best of Both worlds
-- a function that returns a boolean returns exactly a single bit of information: does the relation hold ord does it not? Conversely, the evidence approach tells us exactly why the relation holds, but we are responsible for generating the evidence. But it is easy to define a type that combines the benefits of both approaches. It is called Dec A, where Dec is short for decidable:

data Dec (A : Set) : Set where
  yes  :   A → Dec A
  no   : ¬ A → Dec A
-- Like booleans, we have two cons. A value is either yes x where x provides evidence that A holds, or of the form no ¬x where ¬x provides evidence that A cannot hold (that is, ¬x is a function which given evidence of A yields a contradiction)
-- for example, we define _<=?_ which given two numbers decides wether one is less than or equal to the other, and provides evidence to justofy its conclusion 
-- first, we introduce two functions useful for constructing evidence that an inequality does not hold

¬s≤z : ∀ {m : ℕ} → ¬ (suc m ≤ zero)
¬s≤z ()

¬s≤s : ∀ {m n : ℕ} → ¬ (m ≤ n) → ¬ (suc m ≤ suc n)
¬s≤s ¬m≤n (s≤s m≤n) = ¬m≤n m≤n
-- The first asserts that not (suc m <= zero), and follows by absurdity, since any evidence of inequality has the form zero <= n or suc m <= suc n, neither of which match suc m <= zero. The second takes evidence not m<=n of not (m  <= n) and returns a proof of not (suc m <= suc n). Any evidence of suc m <= suc n must have the form s<=s m<=n where m<=n is evidence that m <= n. Hence, we have a contradiction, evidenced by ¬m<=n m<=n

-- using these, it is straightforward to decide an inequality

_≤?_ : ∀ (m n : ℕ) → Dec (m ≤ n)
zero   ≤? n     = yes z≤n
suc m  ≤? zero  = no ¬s≤z
suc m ≤? suc n with m ≤? n
...         | yes m≤n  = yes (s≤s m≤n)
...         | no ¬m≤n  = no (¬s≤s ¬m≤n)

































