module logical-foundations.Relations where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-comm; +-identityʳ)

-- defining the relation less than or equal:
-- z≤n --------
--     zero ≤ n

--     m ≤ n
-- s≤s -------------
--     suc m ≤ suc n

-- z <= n is the constructor for zero <= n and produces evidence that the proposition holds
-- s<= takes evidence that m<= n holds into evidence that suc m <= suc n holds
data _≤_ : ℕ → ℕ → Set where

  z≤n : ∀ {n : ℕ}
      --------
    → zero ≤ n

  s≤s : ∀ {m n : ℕ}
    → m ≤ n 
      ----------- 
    → suc m ≤ suc n

-- example proof that 2 <= 4:
--  z≤n -----
--       0 ≤ 2
--  s≤s -------
--       1 ≤ 3
-- s≤s ---------
--       2 ≤ 4
-- or in agda:
_ : 2 ≤ 4
_ = s≤s (s≤s z≤n)

-- Implicit arguments
-- in the definition of inequality, the two lines defining the constructors use ∀ , very similar to our use in propositions.
-- +-comm : ∀ (m n : ℕ) → m + n ≡ n + m
-- However, here the declarations are surrounded by curly braces rather than parentheses. This means that the arguments are implicit and need not be wrritten explicitly; instead, they're inferred by Agdas typechecker. Thus, we write +-comm m n for the proof that m + n ≡ n + m, but z≤n for the proof that zero <= n, leaving n implicit. Similarly, if m≤n is evidence that m <= n, we write s≤s m≤n for evidence that suc m <= suc n, leaving both m and n implicit.

infix 4 _≤_ -- binds less tightly than _+_ 

-- Decidability
-- Given two numbers, it is straightforward to compute whether or not the first is less then or equal to the second. We don't give the code for doing so here, but will return to this point on Decidable.

-- Inversion
-- in our definitions, we go from smaller things to larger things. For instance, from m <= n we can conclude suc m <= suc n where suc m is bigger than m (and so for n). But sometimes we want to go from bigger things to smaller.

-- there is only one way to prove that suc m <= suc n for any m and n.
inv-s≤s : ∀ {m n : ℕ}
  → suc m ≤ suc n
    -------------
  → m ≤ n
inv-s≤s (s≤s m≤n) = m≤n

-- here m≤n (without spaces) is a variable name while m <= n is a type, and the latter is the type of the former.
-- Not every rule is invertible. Indeed, the rule for z≤n has no non-implicit hypotheses, so there is nothing to invert. But often inversions of this kind hold.

-- Another example of inversion is showing that there is only one way a number can be less than or equal to zero.
inv-z≤n : ∀ {m : ℕ}
  → m ≤ zero
    --------
  → m ≡ zero
inv-z≤n z≤n = refl

-- Properties of ordering relations
-- Reflexive: for all n, the relation n  <= n holds
-- Transitive: for all m, n and p, if m <= n and n <= p hold, then m <= p holds.
-- Anti-symmetric: for all m and n, if both m <= n and n <= m hold, then m≡n holds
-- total: for all m and n, either m <= n or n <= m holds.

-- we also have names for some combinations of these properties
-- preorder: any order that is reflexive and transitive
-- partial order: any preorder that is also anti-symmetric
-- total order: any partial order that is also total

-- Reflexivity:
≤-refl : ∀ {n : ℕ}
    ------
  → n ≤ n 

≤-refl {zero} = z≤n 
≤-refl {suc n} = s≤s ≤-refl

-- this proof is a induction on the implicit argument n.

-- Transitivity:
≤-trans : ∀ {m n p : ℕ}
  → m ≤ n 
  → n ≤ p   
    ---------
  → m ≤ p

≤-trans z≤n _ = z≤n
≤-trans (s≤s m≤n) (s≤s n≤p)  =  s≤s (≤-trans m≤n n≤p)

-- here the proof is by induction on the evidence that m <= n. In the base case, the first inequality holds by z<=n and must show zero <= p, which follows immediately by z<=n . In this case, the fact that n <= p is irrelevant, and we write _ as the pattern to indicate that the corresponding evidence is unused.

-- In the inductive case, the first inequality holds by s<=s m<=n and the second inequality by s<=s n<=p, and so we are given suc m <= suc n and suc n <= suc p, and must show suc m <= suc p. The inductive hypothesis <=-trans m<=n n<=p establishes that m <= p, and our goal follows by applying s<=s.

-- The case ≤-trans (s≤s m≤n) z≤n cannot arise, since the first inequality implies the middle value is suc n while the second inequality implies that it is zero. Agda can determine that such a case cannot arise, and does not require (or permit) it to be listed.

-- The technique of induction on evidence that a property holds (e.g., inducting on evidence that m ≤ n)—rather than induction on values of which the property holds (e.g., inducting on m)—will turn out to be immensely valuable, and one that we use often.

-- anti-symmetry
≤-antisym : ∀ {m n : ℕ}
  → m ≤ n
  → n ≤ m
    -----
  → m ≡ n
≤-antisym z≤n       z≤n        =  refl
≤-antisym (s≤s m≤n) (s≤s n≤m)  =  cong suc (≤-antisym m≤n n≤m)

