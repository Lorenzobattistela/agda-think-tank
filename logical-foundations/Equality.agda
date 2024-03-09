-- Equality and equational reasoning
module logical-foundations.Equality where
-- showing how to define equality as an inductive datatype

-- for any type A and for any x of type A, the constructor refl provides evidence that x≡x. Hence, every value is equal to itself and we have no other way of showing values equal. The definition features an asymmetry, in that the first arg to ≡ is given by the parameter x : A, while the second is given by and index in A → Set. This follows our policy of using parameters x : A, while the second is given by an index in A → Set . This follows our policy of using parameters wherever possible. The first argument to ≡ can be a parameter because it doesnt vary, while the second must be an index, so it can be required to be equal to the first.

data _≡_ {∀ : Set} (x : A) : A → Set where
    refl : x ≡ x 

infix 4 _≡_

-- equality is an equivalence relation
-- an requivalence relation is one which is reflexive, symmetric and trnaistive. Reflexivity is builtin to the definition of equality, via the constructor refl. It is straightforward to show symmetry:

sym : ∀ {A : Set} {x y : A}
    → x ≡ y 
      ------- 
    → y ≡ x 
sym refl = refl
-- this proof work because the arg to sym has type x ≡ y but on the left-hand side of the equation the argument has been instantiated to the pattern refl, which requires that x and y are the same. Hence, for the right-hand side of the equation we need a term of type x ≡ x and refl will do.
