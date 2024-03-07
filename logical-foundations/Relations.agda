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
-- proof by induction over the evidence that m <= n and n m <= n holds
-- in the base case, both inequalities hold by z<= n, and so we're given zero <= zero and zero <= zero and must show zero ≡ zero, which follows by reflexivity.
≤-antisym : ∀ {m n : ℕ}
  → m ≤ n
  → n ≤ m
    -----
  → m ≡ n
≤-antisym z≤n       z≤n        =  refl
≤-antisym (s≤s m≤n) (s≤s n≤m)  =  cong suc (≤-antisym m≤n n≤m)

-- The above proof omits cases where one argument is z≤n and one argument is s≤s. Why is it ok to omit them?
-- because there is only one way to a num to be <= 0 in nats, n ≡ 0

-- Total
-- for any nats m and n, either m<=n or n<=m or m is equal to n
-- evidence that Total m n holds is either on the form forward m<=n or flipped n<=m where m<=n and n<=m are evidence of m<=n and n<=m respectively.
-- the above definition could also be written as a disjunction (logical or)
-- total is our first use of a datatype with parameters (m and n) which is equivalent to say:
-- data Total : ℕ → ℕ → Set where 
-- and then use m and n inside a forall
-- ∀ {m n : ℕ }
-- each param of the type translates as an implicit param of each constructor. Unlike an indexed datatype, where the index can vary (as in zero <= n and suc m <= n), in a parametrised datatype the params must always be the same (as in Total m n).
data Total (m n : ℕ) : Set where

  forward :
      m ≤ n
      ---------
    → Total m n

  flipped :
      n ≤ m
      ---------
    → Total m n

-- now we can specifiy and prove totality
≤-total : ∀ (m n : ℕ) → Total m n
≤-total zero n = forward z≤n 
≤-total (suc m) zero = flipped z≤n 
≤-total (suc m) (suc n) with ≤-total m n 
...                       | forward m≤n = forward(s≤s m≤n)
...                       | flipped n≤m = flipped(s≤s n≤m)

-- in the first base case, if the first arg is zero and second is n, then the forward case holds, with z<=n as evidence that zero <= n
-- in the second base case, if the first arg is suc m and the second arg is zero, then the flipped case holds, with z<=n as evidence that zero<=suc m
-- in the inductive case: if the first arg is suc m and the second argument is suc n, then the inductive hypothesis <=-total m n establishes one of the following
--  the forward case of the inductive hypothesis holds with m<=n as evidence that m<=n from which it follows that the forward case of the proposition holds with s<=s m<=n as evidence that suc m <= suc n
-- the flipped case of the inductive hypothesis holds with n<=m as evidence that n <= m, from which it follows that the flipped case of the proposition holds with s<=s n<=m as evidence that suc n <= suc m.

-- this is the first time we use the 'with' clause in Agda. The keyword with is followed by an expression and one or more subsequent lines. Each line begins with an ellipsis (...) and a vertical bar (|), followed by a pattern to be matched against the expression and the right-hand side of the equation.

-- every use of with is equivalent to defining a helper function. FOr example, the definition above is equivalent to:
≤-total′ : ∀ (m n : ℕ) → Total m n
≤-total′ zero    n        =  forward z≤n
≤-total′ (suc m) zero     =  flipped z≤n
≤-total′ (suc m) (suc n)  =  helper (≤-total′ m n)
  where
  helper : Total m n → Total (suc m) (suc n)
  helper (forward m≤n)  =  forward (s≤s m≤n)
  helper (flipped n≤m)  =  flipped (s≤s n≤m)

-- This is also the first use of a where clause in Agda. The keyword where is followed by one or more definitions, which must be indented. Any variables bound on the left-hand side of the preceding equation (in this case, m and n) are in scope within the nested definition, and any identifiers bound in the nested definition (in this case, helper) are in scope in the right-hand side of the preceding equation.

-- if both arguments are equal, then both cases hold and we could return evidence of either. In the code above we return the forward case, but there is a variant that returns the flipped case:
≤-total″ : ∀ (m n : ℕ) → Total m n
≤-total″ m       zero                      =  flipped z≤n
≤-total″ zero    (suc n)                   =  forward z≤n
≤-total″ (suc m) (suc n) with ≤-total″ m n
...                         | forward m≤n  =  forward (s≤s m≤n)
...                         | flipped n≤m  =  flipped (s≤s n≤m)


-- Monotonicity

-- If one 