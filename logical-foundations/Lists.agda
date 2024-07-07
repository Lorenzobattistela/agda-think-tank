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

























