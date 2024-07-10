module logical-foundations.Lists where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong)
open Eq.≡-Reasoning
open import Data.Bool using (Bool; true; false; T; _∧_; _∨_; not)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _≤_; s≤s; z≤n)
open import Data.Nat.Properties using
  (+-assoc; +-identityˡ; +-identityʳ; *-assoc; *-identityˡ; *-identityʳ; *-distribʳ-+)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Data.Product using (_×_; ∃; ∃-syntax) renaming (_,_ to ⟨_,_⟩)
open import Function using (_∘_)
open import Level using (Level)
open import logical-foundations.Isomorphism using (_≃_; _⇔_)

-- lists:
-- If A is a set, then List A is a set. (list w elements of type A). 
-- The empty list is a list of type A
-- The cons operator takes a value of type A and a value of type List A and returns other value of type List A
data List (A : Set) : Set where
  [] : List A
  _∷_ : A → List A → List A

infixr 5 _∷_

_ : List ℕ
_ = 0 ∷ 1 ∷ 2 ∷ []

-- including the pragma: tells agda that List corresponds to the haskell type list, and [] and :: correspond to nil and cons
{-# BUILTIN LIST List #-}

-- List syntax:
pattern [_] z = z ∷ []
pattern [_,_] y z = y ∷ z ∷ []
pattern [_,_,_] x y z = x ∷ y ∷ z ∷ []
pattern [_,_,_,_] w x y z = w ∷ x ∷ y ∷ z ∷ []
pattern [_,_,_,_,_] v w x y z = v ∷ w ∷ x ∷ y ∷ z ∷ []
pattern [_,_,_,_,_,_] u v w x y z = u ∷ v ∷ w ∷ x ∷ y ∷ z ∷ []
pattern [_] z = z ∷ []
pattern [_,_] y z = y ∷ z ∷ []
pattern [_,_,_] x y z = x ∷ y ∷ z ∷ []
pattern [_,_,_,_] w x y z = w ∷ x ∷ y ∷ z ∷ []
pattern [_,_,_,_,_] v w x y z = v ∷ w ∷ x ∷ y ∷ z ∷ []
pattern [_,_,_,_,_,_] u v w x y z = u ∷ v ∷ w ∷ x ∷ y ∷ z ∷ []

-- append
infixr 5 _++_

_++_ : ∀ {A : Set} → List A → List A → List A
[]       ++ ys  =  ys
(x ∷ xs) ++ ys  =  x ∷ (xs ++ ys)
-- the type A is an implicit argument to append, making it a polymorphic function
-- you receive two lists of A and return another one


_ : [ 0 , 1 , 2 ] ++ [ 3 , 4 ] ≡ [ 0 , 1 , 2 , 3 , 4 ]
_ = refl

-- we can reason about lists in much the same way that we reason about numbers.
++-assoc : ∀ {A : Set} (xs ys zs : List A)
  → (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
++-assoc [] ys zs =
  begin
    ([] ++ ys) ++ zs
  ≡⟨⟩
    ys ++ zs
  ≡⟨⟩
    [] ++ (ys ++ zs)
  ∎
++-assoc (x ∷ xs) ys zs =
  begin
    (x ∷ xs ++ ys) ++ zs
  ≡⟨⟩
    x ∷ (xs ++ ys) ++ zs
  ≡⟨⟩
    x ∷ ((xs ++ ys) ++ zs)
  ≡⟨ cong (x ∷_) (++-assoc xs ys zs) ⟩
    x ∷ (xs ++ (ys ++ zs))
  ≡⟨⟩
    x ∷ xs ++ (ys ++ zs)
  ∎
-- proof by induction on first arg.

-- we can also show that [] is a left and a right identity for ++.
++-identityˡ : ∀ {A : Set} (xs : List A) → [] ++ xs ≡ xs
++-identityˡ xs =
  begin
    [] ++ xs
  ≡⟨⟩
    xs
  ∎
-- and the right id follows by induction
++-identityʳ : ∀ {A : Set} (xs : List A) → xs ++ [] ≡ xs
++-identityʳ [] =
  begin
    [] ++ []
  ≡⟨⟩
    []
  ∎
++-identityʳ (x ∷ xs) =
  begin
    (x ∷ xs) ++ []
  ≡⟨⟩
    x ∷ (xs ++ [])
  ≡⟨ cong (x ∷_) (++-identityʳ xs) ⟩
    x ∷ xs
  ∎
-- these three properties establish that _++_ and [] form a monoid over lists

-- defining length
length : ∀ {A : Set} → List A → ℕ
length [] = zero
length (x ∷ xs) = 1 + length xs

_ : length [ 1 , 2 ] ≡ 2
_ = refl

-- we can also reason about length: 
-- the length of one list appended to another is the sum of the lengths of the list
length-++ : ∀ {A : Set} (xs ys : List A)
  → length (xs ++ ys) ≡ length xs + length ys
length-++ {A} [] ys =
  begin
    length ([] ++ ys)
  ≡⟨⟩
    length ys
  ≡⟨⟩
    length {A} [] + length ys
  ∎
length-++ (x ∷ xs) ys =
  begin
    length ((x ∷ xs) ++ ys)
  ≡⟨⟩
    suc (length (xs ++ ys))
  ≡⟨ cong suc (length-++ xs ys) ⟩
    suc (length xs + length ys)
  ≡⟨⟩
    length (x ∷ xs) + length ys
  ∎
-- proof by induction on the first argument. Base case instantiates to [], follows by computation. Inductive instantiates to x :: xs

-- reversing a list:
reverse : ∀ {A : Set} → List A → List A
reverse [] = []
reverse (x ∷ xs) = (reverse xs) ++ [ x ] 

_ : reverse [ 1 , 2 ] ≡ [ 2 , 1 ]
_ = refl
-- this way of reversing takes quadratic time in the length of the lsit


-- a faster reverse: we generalise it to take an additional argument
-- basically works the same way as folding in bend, you use an acc
shunt : ∀ {A : Set} → List A → List A → List A
shunt []    ys = ys
shunt (x ∷ xs) ys = shunt xs (x ∷ ys)

_ : shunt ([ 1 , 2 , 3 ]) ([ 4 , 5 ]) ≡ (3 ∷ 2 ∷ 1 ∷ 4 ∷ 5 ∷ [])
_ = refl

-- but note that we need two functions to do the reverse, and with fold we could declare the acc right away
reverse′ : ∀ {A : Set} → List A → List A
reverse′ xs = shunt xs []

_ : reverse′ [ 1 , 2 ] ≡ [ 2 , 1 ]
_ = refl
-- now the time to reverse a list is linear in the length of the list

-- Map
-- map applies a function to every element of a list to generate a corresponding list: it is a higher order function, which takes a function as an argument or returns a function as a result

map : ∀ {A B : Set} → (A → B) → List A → List B
map f [] = []
map f (x ∷ xs) = f x ∷ map f xs

_ : reverse′ [ [ 1 ] , [ 2 ] ] ≡ [ [ 2 ] , [ 1 ] ]
_ = refl

-- example: map reverse
_ : map reverse′ [ [ 1 , 2 ] , [ 2 , 1 ] ] ≡ [ [ 2 , 1 ] , [ 1 , 2 ] ]
_ = refl

data Tree (A B : Set) : Set where
  leaf : A → Tree A B
  node : Tree A B → B → Tree A B → Tree A B

-- kinda bad visual representation but works. A better syntax to construct would help
map-Tree : ∀ {A B C D : Set} → (A → C) → (B → D) → Tree A B → Tree C D
map-Tree f g (leaf x) = leaf (f x)
map-Tree f g (node l x r) = node (map-Tree f g l) (g x) (map-Tree f g r)

_ : map-Tree suc not (node (leaf 1) true (node (leaf 2) false (leaf 3))) ≡ 
              node (leaf 2) false (node (leaf 3) true  (leaf 4))
_ = refl


-- Fold
-- Takes an operator and a values, and uses the operator to combine each element of the elements of the list, taking the
-- given value as the result for the empty list
foldr : ∀ {A B : Set} → (A → B → B) → B → List A → B
foldr _⊕_ e [] = e
foldr _⊕_ e (x ∷ xs) = x ⊕ foldr _⊕_ e xs

fold-Tree : ∀ {A B C : Set} → (A → C) → (C → B → C → C) → Tree A B → C
fold-Tree f g (leaf x) = f x
fold-Tree f g (node l x r) = g (fold-Tree f g l) x (fold-Tree f g r)

-- example of using fold to find the sum of a list
-- in this case we have an instance of foldr where A and B are both ℕ. Fold requires time linear in the length of the list
_ : foldr _+_ 0 [ 1 , 2 , 3 , 4 ] ≡ 10
_ =
  begin
    foldr _+_ 0 (1 ∷ 2 ∷ 3 ∷ 4 ∷ [])
  ≡⟨⟩
    1 + foldr _+_ 0 (2 ∷ 3 ∷ 4 ∷ [])
  ≡⟨⟩
    1 + (2 + foldr _+_ 0 (3 ∷ 4 ∷ []))
  ≡⟨⟩
    1 + (2 + (3 + foldr _+_ 0 (4 ∷ [])))
  ≡⟨⟩
    1 + (2 + (3 + (4 + foldr _+_ 0 [])))
  ≡⟨⟩
    1 + (2 + (3 + (4 + 0)))
  ∎

-- it is often convenient to exploit currying by applying fold to an operator and a value to yield a new function 
sum : List ℕ → ℕ
sum = foldr _+_ 0

_ : sum [ 1 , 2 , 3 , 4 ] ≡ 10
_ =
  begin
    sum [ 1 , 2 , 3 , 4 ]
  ≡⟨⟩
    foldr _+_ 0 [ 1 , 2 , 3 , 4 ]
  ≡⟨⟩
    10
  ∎

product : List ℕ → ℕ
product = foldr _*_ 1

_ : product [ 1 , 2 , 3 ] ≡ 6
_ = refl

-- Monoids
-- typically when we use a fold the operator is associative and the value is a left and right identity for the operator
-- meaning that the oeprator and the value form a monoid

record IsMonoid {A : Set} (_⊕_ : A → A → A) (e : A) : Set where
  field
    assoc : ∀ (x y z : A) → (x ⊕ y) ⊕ z ≡ x ⊕ (y ⊕ z)
    identityˡ : ∀ (x : A) → e ⊕ x ≡ x
    identityʳ : ∀ (x : A) → x ⊕ e ≡ x
open IsMonoid

-- as examples, sum and zero, multiplication and one, append and the empty list are all examples of monoids:
+-monoid : IsMonoid _+_ 0
+-monoid =
  record
    { assoc = +-assoc
    ; identityˡ = +-identityˡ
    ; identityʳ = +-identityʳ
    }

*-monoid : IsMonoid _*_ 1
*-monoid =
  record
    { assoc = *-assoc
    ; identityˡ = *-identityˡ
    ; identityʳ = *-identityʳ
    }

++-monoid : ∀ {A : Set} → IsMonoid {List A} _++_ []
++-monoid =
  record
    { assoc = ++-assoc
    ; identityˡ = ++-identityˡ
    ; identityʳ = ++-identityʳ
    }

-- All
-- We can also define predicates over lists. Two of the most important are All and Any
-- Predicate All P holds if predicate P is satisfied by every element of a list

data All {A : Set} (P : A → Set) : List A → Set where
  [] : All P []
  _∷_ : ∀ {x : A} {xs : List A} → P x → All P xs → All P (x ∷ xs)

-- example: All (_≤ 2) holds of a list where every element is less than or eq to two
_ : All (_≤ 2) [ 0 , 1 , 2 ]
_ = z≤n ∷ s≤s z≤n ∷ s≤s (s≤s z≤n) ∷ []

-- Any
-- Predicate Any P holds if predicate P is satisfied by some element of a list
data Any {A : Set} (P : A → Set) : List A → Set where
  here : ∀ {x : A} {xs : List A} → P x → Any P (x ∷ xs)
  there : ∀ {x : A} {xs : List A} → Any P xs → Any P (x ∷ xs)
-- the first constructor provides evidence that the head of the list satisfies P, while the second provides evidence that some element of the tail of the list satisfies P. Example of list membership definition:

infix 4 _∈_ _∉_

_∈_ : ∀ {A : Set} (x : A) (xs : List A) → Set
x ∈ xs = Any (x ≡_) xs

_∉_ : ∀ {A : Set} (x : A) (xs : List A) → Set
x ∉ xs = ¬ (x ∈ xs)

_ : 0 ∈ [ 0 , 1 , 0 , 2 ]
_ = here refl

_ : 0 ∈ [ 0 , 1 , 0 , 2 ]
_ = there (there (here refl))

-- All and append:
-- a predicate holds for every element of one list appended to another if and only if it holds for every element of both lists
All-++-⇔ : ∀ {A : Set} {P : A → Set} (xs ys : List A) →
  All P (xs ++ ys) ⇔ (All P xs × All P ys)
All-++-⇔ xs ys =
  record
    { to       =  to xs ys
    ; from     =  from xs ys
    }
  where

  to : ∀ {A : Set} {P : A → Set} (xs ys : List A) →
    All P (xs ++ ys) → (All P xs × All P ys)
  to [] ys Pys = ⟨ [] , Pys ⟩
  to (x ∷ xs) ys (Px ∷ Pxs++ys) with to xs ys Pxs++ys
  ... | ⟨ Pxs , Pys ⟩ = ⟨ Px ∷ Pxs , Pys ⟩

  from : ∀ { A : Set} {P : A → Set} (xs ys : List A) →
    All P xs × All P ys → All P (xs ++ ys)
  from [] ys ⟨ [] , Pys ⟩ = Pys
  from (x ∷ xs) ys ⟨ Px ∷ Pxs , Pys ⟩ =  Px ∷ from xs ys ⟨ Pxs , Pys ⟩

-- Decidability of All
-- if we consider a predicate as a functino that yields a boolean, it is easy to define an analogue of All
all : ∀ {A : Set} → (A → Bool) → List A → Bool
all p  =  foldr _∧_ true ∘ map p

-- if we replace booleans by decidables there is again an analogue of All. First, return to the notion of a predicate P as a function of type A → Set, taking a value x of type A into evidence P x that a property holds for x. Say that a predicate P is decidable if we have a function that for a given x can decide P x:
Decidable : ∀ {A : Set} → (A → Set) → Set
Decidable {A} P  =  ∀ (x : A) → Dec (P x)
-- Then if predicate P is decidable, it is also decidable whether every element of a list satisfies the predicate:
All? : ∀ {A : Set} {P : A → Set} → Decidable P → Decidable (All P)
All? P? []                                 =  yes []
All? P? (x ∷ xs) with P? x   | All? P? xs
...                 | yes Px | yes Pxs     =  yes (Px ∷ Pxs)
...                 | no ¬Px | _           =  no λ{ (Px ∷ Pxs) → ¬Px Px   }
...                 | _      | no ¬Pxs     =  no λ{ (Px ∷ Pxs) → ¬Pxs Pxs }

-- If the list is empty, then trivially P holds for every element of the list. Otherwise, the structure of the proof is similar to that showing that the conjunction of two decidable propositions is itself decidable, using _∷_ rather than ⟨_,_⟩ to combine the evidence for the head and tail of the list.














