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

-- exercise _<?_


-- Erasure takes a decidable value to a boolean:
[_] : ∀ {A : Set} → Dec A → Bool
[ yes x ] = true
[ no ¬x ] = false

-- using erasure, its easy to derive _≤ᵇ_ from _≤?_
_≤ᵇ′_ : ℕ → ℕ → Bool
m ≤ᵇ′ n = [ m ≤? n ]

-- further, if D is a value of type Dec A, then T [ D ] is inhabited exactly when A is inhabited
--(remembering that inhabited refers to a type that has at least one value or element)
toWitness : ∀ {A : Set} {D : Dec A} → T [ D ] → A
toWitness {A} {yes x} tt = x
toWitness {A} {no ¬x} ()

fromWitness : ∀ {A : Set} {D : Dec A} → A → T [ D ]
fromWitness {A} {yes x} _ = tt
fromWitness {A} {no ¬x} x = ¬x x

-- and using these, we can easily derive that T (m ≤ᵇ′ n) is inhabited exactly when m ≤ n is inhabited:
≤ᵇ′→≤ : ∀ {m n : ℕ} → T (m ≤ᵇ′ n) → m ≤ n
≤ᵇ′→≤ = toWitness

≤→≤ᵇ′ : ∀ {m n : ℕ} → m ≤ n → T (m ≤ᵇ′ n)
≤→≤ᵇ′ = fromWitness

-- Logical Connectives
-- Each one extends to decidables:
infixr 6 _∧_
_∧_ : Bool → Bool → Bool
true ∧ true = true
false ∧ _   = false
_ ∧ false   = false

-- correspondingly, given two decidable propositions, we can decide their conjunction:
infixr 6 _×-dec_

-- the conjunction of two propositons hold if they both hold, and its negation holds if the negation of either holds.
-- If both hold, we pair the evidence for each to yield evidence of the conjunct
-- If the negation of either holds, assuming the conjunct will lead to a contradiction.
_×-dec_ : ∀ {A B : Set} → Dec A → Dec B → Dec (A × B)
yes x ×-dec yes y = yes ⟨ x , y ⟩
no ¬x ×-dec _     = no λ{ ⟨ x , y ⟩ → ¬x x }
_     ×-dec no ¬y = no λ{ ⟨ x , y ⟩ → ¬y y }


infixr 5 _v_

_v_ : Bool → Bool → Bool
true v _      = true
_    v true   = true
false v false = false

-- correspondingly, given two decidable propositions we can decide their disjunction
infixr 5 _⊎-dec_

-- the disjunction of two propositions holds if either holds, and its negation holds if the negation of both hold. If either holds, we inject the evidence to yield evidence of the disjunct.
-- If the negation of both hold, assuming either disjunct will lead to a contradiction.
_⊎-dec_ : ∀ {A B : Set} → Dec A → Dec B → Dec (A ⊎ B)
yes x ⊎-dec _     = yes (inj₁ x)
_     ⊎-dec yes y = yes (inj₂ y)
no ¬x ⊎-dec no ¬y = no λ{ (inj₁ x) → ¬x x ; (inj₂ y) → ¬y y }

not : Bool → Bool
not true = false
not false = true

-- just swap yes and no
¬? : ∀ {A : Set} → Dec A → Dec (¬ A)
¬? (yes x) = no (¬¬-intro x)
¬? (no ¬x) = yes ¬x

_⊃_ : Bool → Bool → Bool
_     ⊃ true  = true
false ⊃ _     = true
true  ⊃ false = false

-- we can decide if the first implies the second
-- the implication holds if either the second hols or the negation of the first holds, and its negation holds if the first holds
-- and the negation of the seoncd holds. Evidence for the implication is a function from evidence of the first to evidence of the second. If the second holds, the funciton returns the evidence for it. If the negation of the first holds, the function takes the evidence of the first and derives a contradiction. If the first holds and the negation of the secon d holds, given evidence of the implication we must derive a contradiction; we apply the evidence of the implication f to the evidence of the first x, yielding a contradictiion with the evidence ¬y of the negation of the second
_→-dec_ : ∀ {A B : Set} Dec A → Dec B → Dec (A → B)
_  →-dec yes y = yes (λ _ → y)  
no ¬x →-dec _  = yes (λ x → ⊥-elim (¬x x))
yes x →-dec no ¬y = no (λ f → ¬y (f x)) 


-- Proof by Reflection: Lets revisit the monus definition from Naturals. If subtracting a larger number from a smaller, we take the result to 0. We could have defined a guarded version of minus, a function which subtracts n from m only if n ≤ m:
minus : (m n : ℕ) (n≤m : n ≤ m) → ℕ
minus m zero _ = m
minus (suc m) (suc n) (s≤s n≤m) = minus m n n≤m
-- but this is painful to use:
_ : minus 5 3 (s≤s (s≤s (s≤s z≤n))) ≡ 2
_ = refl

-- we cant solve this in general, but in the scenario above we happen to know the two numbers statically. In that case, we can use a technique called proof by reflection. Essentially, we can ask agda to run the decidable equality n ≤? m while type checking and make sure n ≤ m!
-- We do this through the use of implicits. Agda will fill in an implicit of a record type if it can fill in all its fields. So Agda will always manage to fill in an implicit of an empty record type, since there are not any fields. This is why T is defined as an empty record.
-- The trick is to have an implicit arg of type T [ n ≤? m ]. What this means?
-- First, we run the decision procedure, n≤?m, which provides us evidence wether n≤m holds or not. We erase the evidence to a boolean. Finally, we apply T. Recall that T maps booleans into the world of evidence: true becomes the unit type T, and false becomes the empty type ⊥. Operationally, an implicit arg of this type works as a guard.
-- If n <= m holds, the type of the implicit value reduces to T. Agda then provides the implicit value.
-- Otherwise, the type reduces to ⊥ which Agda has no chance of providing, so it will throw an error. 
-- We obtain the witness for n <= m using toWitness, which we defined earlier:
_-_ : (m n : ℕ) {n≤m : T [ n ≤? m ]} → ℕ
_-_ m n {n≤m} = minus m n (toWitness n≤m)

-- now we can safely use _-_ as long as we know the two numbers statically
_ : 5 - 3 ≡ 2
_ = refl

-- this idiom is very common, and the STD defines a synonym for T [ ? ] called True
True : ∀ {Q} → Dec Q → Set
True Q = T [ Q ]








