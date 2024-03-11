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

module ≡-Reasoning {A : Set} where

  infix  1 begin_
  infixr 2 _≡⟨⟩_ step-≡
  infix  3 _∎

  begin_ : ∀ {x y : A}
    → x ≡ y
      -----
    → x ≡ y
  begin x≡y  =  x≡y

  _≡⟨⟩_ : ∀ (x : A) {y : A}
    → x ≡ y
      -----
    → x ≡ y
  x ≡⟨⟩ x≡y  =  x≡y

  step-≡ : ∀ (x {y z} : A) → y ≡ z → x ≡ y → x ≡ z
  step-≡ x y≡z x≡y  =  trans x≡y y≡z

  syntax step-≡ x y≡z x≡y  =  x ≡⟨  x≡y ⟩ y≡z

  _∎ : ∀ (x : A)
      -----
    → x ≡ x
  x ∎  =  refl

open ≡-Reasoning

-- this is our first use of a nested module. It is module keyword followed by the module name and any paramters, explicit or implicit, the keyword where and the contents of the module indented. Modules may contain any sort of declaration, including other nested modules. Opening the module maks all of the definitions available in the current environment.
-- this is also the first use of a syntax declaration which specifies that the term on the left may be written with the syntax on the right. The syntax x ≡⟨ x≡y ⟩ y≡z inherits the fixity infixr 2 declared for step-≡ and the special syntax is available when the identifier step is imported.

-- lets proof transitivity as a chain oif equations

trans′ : ∀ {A : Set} {x y z : A}
  → x ≡ y
  → y ≡ z
    -----
  → x ≡ z

trans′ {A} {x} {y} {z} x≡y y≡z =
  begin
    x
  ≡⟨ x≡y ⟩
    y
  ≡⟨ y≡z ⟩
    z
  ∎

-- The application of begin is purely cosmetic, as it simply returns its argument. That argument consists of _≡⟨_⟩_ applied to x, x≡y, and y ≡⟨ y≡z ⟩ (z ∎). The first argument is a term, x, while the second and third arguments are both proofs of equations, in particular proofs of x ≡ y and y ≡ z respectively, which are combined by trans in the body of _≡⟨_⟩_ to yield a proof of x ≡ z. The proof of y ≡ z consists of _≡⟨_⟩_ applied to y, y≡z, and z ∎. The first argument is a term, y, while the second and third arguments are both proofs of equations, in particular proofs of y ≡ z and z ≡ z respectively, which are combined by trans in the body of _≡⟨_⟩_ to yield a proof of y ≡ z. Finally, the proof of z ≡ z consists of _∎ applied to the term z, which yields refl. After simplification, the body is equivalent to the term:

-- trans x≡y (trans y≡z refl)
-- We could replace any use of a chain of equations by a chain of applications of trans; the result would be more compact but harder to read. The trick behind ∎ means that a chain of equalities simplifies to a chain of applications of trans that ends in trans e refl, where e is a term that proves some equality, even though e alone would do.

-- another example: repeat the proof that addition is commutative. 
data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

_+_ : ℕ → ℕ → ℕ
zero    + n  =  n
(suc m) + n  =  suc (m + n)

postulate
  +-identity : ∀ (m : ℕ) → m + zero ≡ m
  +-suc : ∀ (m n : ℕ) → m + suc n ≡ suc (m + n)

-- this is our first use of a postulate. It specifies a signature for an identifier but no definition. Here we postulate something proved earlier to save space. Postulates must be used with caution, because if postulating something false then we could use Agda to prove anything.

+-comm : ∀ (m n : ℕ) → m + n ≡ n + m
+-comm m zero =
  begin
    m + zero
  ≡⟨ +-identity m ⟩
    m
  ≡⟨⟩
    zero + m
  ∎
+-comm m (suc n) =
  begin
    m + suc n
  ≡⟨ +-suc m n ⟩
    suc (m + n)
  ≡⟨ cong suc (+-comm m n) ⟩
    suc (n + m)
  ≡⟨⟩
    suc n + m
  ∎

-- Rewriting
-- Consider a property of natural numbers, such as being even:
data even : ℕ → Set
data odd  : ℕ → Set

data even where

  even-zero : even zero

  even-suc : ∀ {n : ℕ}
    → odd n
      ------------
    → even (suc n)

data odd where
  odd-suc : ∀ {n : ℕ}
    → even n
      -----------
    → odd (suc n)
  
-- in the previous section, we proved addition is commutative given evidence that even (m + n) holds, we ought also to be able to take that as evidence that even (n + m) holds.
-- Agda includes special notation to support just this kind of reasoning. The rewrite notation. 
{-# BUILTIN EQUALITY _≡_ #-}

-- And we can prove the property as follows
even-comm : ∀ (m n : ℕ)
  → even (m + n)
    ------------
  → even (n + m)
even-comm m n ev  rewrite +-comm n m  =  ev
-- here ev ranges over evidence that even(m + n) holds, and we show that it also provides evidence that (even n + m) holds. In general, the keyowrd rewrite is followed by evidence of an equality and that equality is used to rewrite the type of the goal and of any variable in scope. 

-- multiple rewrites
-- one may perform multiple rewrites, each separated by a vertical bar. For example, here is a second proof that addition is commutative, relying on rewrites:
+-comm′ : ∀ (m n : ℕ) → m + n ≡ n + m
+-comm′ zero    n  rewrite +-identity n             =  refl
+-comm′ (suc m) n  rewrite +-suc n m | +-comm′ m n  =  refl

-- The rewrite notation is in fact shorthand for an appropriate use of with abstraction:
even-comm′ : ∀ (m n : ℕ)
  → even (m + n)
    ------------
  → even (n + m)
even-comm′ m n ev with   m + n  | +-comm m n
...                  | .(n + m) | refl       = ev
-- In general, one can follow with by any number of expressions, separated by bars, where each following equation has the same number of patterns. We often write expressions and the corresponding patterns so they line up in columns, as above. Here the first column asserts that m + n and n + m are identical, and the second column justifies that assertion with evidence of the appropriate equality. Note also the use of the dot pattern, .(n + m). A dot pattern consists of a dot followed by an expression, and is used when other information forces the value matched to be equal to the value of the expression in the dot pattern. In this case, the identification of m + n and n + m is justified by the subsequent matching of +-comm m n against refl. One might think that the first clause is redundant as the information is inherent in the second clause, but in fact Agda is rather picky on this point

-- Leibniz equality
-- the form of asserting equality that we have used is due to martin lof, and was published in 1975. An older form is due to Leibniz and published in 1686. He asserted the identitiy of indiscernibles: two objects are qual if and only if they satisfy the same properties. Here we define leibniz equality and show that two terms satisfy leibniz equality if and only if satisfy martin lofs equality. 
-- Leibniz equality is usually formalised to state that x ≐ y holds if every property P that holds of x also holds of y. 
-- Let x and y be objects of type A. We say that x ≐ y holds if for every predicate P over type A we have that P x implies P y
_≐_ : ∀ {A : Set} (x y : A) → Set₁
_≐_ {A} x y = ∀ (P : A → Set) → P x → P y
-- We cannot write the left-hand side of the equation as x ≐ y, and instead we write _≐_ {A} x y to provide access to the implicit parameter A which appears on the right-hand side.
-- this is our first use of levels. We cannot assign Set the type Set, since this would lead to contradictions such as russels paradox. Instead, there is a hierarchy of types, where Set : Set₁, Set₁ : Set₂ and so on.

-- leibniz equality is reflexive and transitive, where the first follows by a variant of the identity function and the second by a variant of function composition.

refl-≐ : ∀ {A : Set} {x : A}
  → x ≐ x
refl-≐ P Px  =  Px

trans-≐ : ∀ {A : Set} {x y z : A}
  → x ≐ y
  → y ≐ z
    -----
  → x ≐ z
trans-≐ x≐y y≐z P Px  =  y≐z P (x≐y P Px)

-- symmetry is less obvious. We have to show that if P x implies P y for all predicates P, then the implication holds the other way round as well:
sym-≐ : ∀ {A : Set} {x y : A}
  → x ≐ y
    -----
  → y ≐ x
sym-≐ {A} {x} {y} x≐y P  =  Qy
  where
    Q : A → Set
    Q z = P z → P x
    Qx : Q x
    Qx = refl-≐ P
    Qy : Q y
    Qy = x≐y Q Qx
  
-- Given x ≐ y, a specific P , we have to construct a proof that P y implies P x. To do so, we insantiate the equality with a predicate Q such that Q z holds if P z implies P x. The property Q x is trivial by reflexivity and hence Q y follows from x ≐ y . But Q y is exactly a proof of what we require, that P y implies P x.

-- We now show that martin-lof equality implies leibniz equality, and vice versa. In the forward direction, if we know x ≡ y we need for any P to take evidence of P x to evidenc of P y, which is easy since equality ox x and y implies that any proof of P x is also a proof of P y:

≡-implies-≐ : ∀ {A : Set} {x y : A}
  → x ≡ y
    -----
  → x ≐ y
≡-implies-≐ x≡y P  =  subst P x≡y

-- This direction follows from substitution, which we showed earlier.
-- In the reverse direction, given that for any P we can take a proof of P x to a proof of P y we need to show x ≡ y:
≐-implies-≡ : ∀ {A : Set} {x y : A}
  → x ≐ y
    -----
  → x ≡ y
≐-implies-≡ {A} {x} {y} x≐y  =  Qy
  where
    Q : A → Set
    Q z = x ≡ z
    Qx : Q x
    Qx = refl
    Qy : Q y
    Qy = x≐y Q Qx

-- The proof is similar to that for symmetry of leibniz equality. We take Q to be the predicate that holds of z if x ≡ z. Then Q x is trivial by reflexivity of Martin Lof equality, and hence Q y follows from x ≐ y. But Q y is exactly a proof of what we require, that x ≡ y.

-- Universe Polymorphism
-- As we have seen, not every type belongs to Set, but instead every type belongs somewhere in the hierarchy set0, set1, set2 and so on;
-- The definition of equality above is fine if we want to compare two values of a type that belongs to Set, but what if we want to compare two values of a type that belongs to Set l for some arbitrary level l?

-- The answer is universe polymorphism, where a definition is made with respect to an arbitrary level l. To make use of levels, we first import the following:

open import Level using (Level; _⊔_) renaming (zero to lzero; suc to lsuc)

-- we rename constructors zero and suc to lzero and lsuc to avoid confusion between levels and naturals.
-- levels are isomorphic to natural numbers, and have similar constructors:

-- lzero : Level
-- lsuc : Level → Level

-- The names set0, set1, set2 are abbreviations for
-- Set lzero
-- Set (lsuc lzero)
-- Set (lsuc (lsuc lzero))
-- and there is also an operator:
-- _⊔_ : Level → Level → Level
-- that given two levels return the larger of the two

-- here is the definition of equality, generalised to an arbitrary level:
data _≡′_ {ℓ : Level} {A : Set ℓ} (x : A) : A → Set ℓ where
  refl′ : x ≡′ x

-- similarly, here is the generalised definition of symmetry:
sym′ : ∀ {ℓ : Level} {A : Set ℓ} {x y : A}
  → x ≡′ y
    ------
  → y ≡′ x
sym′ refl′ = refl′

-- for simplicity, we avoid universe polymorphism in the definitions given in the text, but most definitions in the standard library, including those for equality are generalised to arbitrary levels as above
-- here is the generalised definition of Leibniz equality
_≐′_ : ∀ {ℓ : Level} {A : Set ℓ} (x y : A) → Set (lsuc ℓ)
_≐′_ {ℓ} {A} x y = ∀ (P : A → Set ℓ) → P x → P y

-- before the signature used Set_1 as the type of a term that includes Set, whereas here the signature uses Set (lsuc l) as the type of a term that includes Set l.
-- Most other functions in the standard library are also generalised to arbitrary levels. For instance, here is the definition of composition.

_∘_ : ∀ {ℓ₁ ℓ₂ ℓ₃ : Level} {A : Set ℓ₁} {B : Set ℓ₂} {C : Set ℓ₃}
  → (B → C) → (A → B) → A → C
(g ∘ f) x  =  g (f x)


