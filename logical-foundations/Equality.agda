-- Equality and equational reasoning
module logical-foundations.Equality where
-- showing how to define equality as an inductive datatype

-- for any type A and for any x of type A, the constructor refl provides evidence that x≡x. Hence, every value is equal to itself and we have no other way of showing values equal. The definition features an asymmetry, in that the first arg to ≡ is given by the parameter x : A, while the second is given by and index in A → Set. This follows our policy of using parameters x : A, while the second is given by an index in A → Set . This follows our policy of using parameters wherever possible. The first argument to ≡ can be a parameter because it doesnt vary, while the second must be an index, so it can be required to be equal to the first.

data _≡_ {A : Set} (x : A) : A → Set where
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

-- transitivity is equally straightforward
trans : ∀ {A : Set} {x y z : A}
  → x ≡ y 
  → y ≡ z 
    ------- 
  → x ≡ z 
trans refl refl = refl 

-- Congruence and substitution
-- equality satisfies congruence. If two terms are equal, they remain so after the same function is applied to both:
cong : ∀ {A B : Set} (f : A → B) {x y : A}
  → x ≡ y 
    ----------- 
  → f x ≡ f y 
cong f refl = refl 

-- congruence of functions with two arguments is similar
cong₂ : ∀ {A B C : Set} (f : A → B → C) {u x : A} {v y : B}
  → u ≡ x 
  → v ≡ y 
    -------------- 
  → f u v ≡ f x y 
cong₂ f refl refl = refl 

-- equality is also a congruence in the function position of an application. If two functions are equal, then applying them to the same term yields equal terms:
cong-app : ∀ {A B : Set} {f g : A → B}
  → f ≡ g 
    ----------------------
  → ∀ (x : A) → f x ≡ g x 
cong-app refl x = refl

-- equality also satisfies substitution. If two values are equal and a predicate holds of the first then it also holds of the second
subst : ∀ {A : Set} {x y : A} (P : A → Set)
  → x ≡ y 
    ---------- 
  → P x → P y 
subst P refl px = px
-- a predicate is a proposition over values of some type A, and since we model propositions as types, a predicate is a type parametrized in A. As an example, even : ℕ → Set and odd : ℕ → Set from Relations are predicates on natural number ℕ. (We compare representing predicates as data types A → Set versus functions to booleans A → Bool in Decidable.)

-- Chains of Equations