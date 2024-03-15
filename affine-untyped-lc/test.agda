module affine-untyped-lc.test where

open import Data.Bool using (if_then_else_; Bool; true; false; _∧_)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _≟_)
open import Data.List using (List; _∷_; []; tail)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (Dec; yes; no)
open import Induction.WellFounded using (Acc; acc)

data Term : Set where
    var : ℕ → Term
    lam : Term → Term
    app : Term → Term → Term

Context : Set
Context = List Bool

lookup : ℕ → Context → Bool
lookup x [] = false
lookup zero (b ∷ ctx) = b
lookup (suc x) (b ∷ ctx) = lookup x ctx

consume : ℕ → Context → Context
consume x [] = []
consume zero (b ∷ ctx) = false ∷ ctx
consume (suc x) (b ∷ ctx) = b ∷ consume x ctx

affine : Context → Term → Bool × Context
affine ctx (var x) = if lookup x ctx then (true , consume x ctx) else (false , ctx)

affine ctx (lam t) with affine (true ∷ ctx) t
... | (b , []) = (b , [])
... | (b , (_ ∷ xs)) = (b , xs)

affine ctx (app t u) = 
    let (b1 , ctx1) = affine ctx t
        (b2 , ctx2) = affine ctx1 u
    in (b1 ∧ b2 , ctx2)

affine_term : Term
affine_term = lam ( var 0 ) 

is_affine : Bool × Context
is_affine = affine [] affine_term

is_affine_bool : Bool
is_affine_bool = proj₁ is_affine

affine-is-affine : is_affine_bool ≡ true
affine-is-affine = refl

not-affine-term : Term
not-affine-term = lam (app (var 0) (var 0))

not-affine-is-affine : Bool × Context
not-affine-is-affine = affine [] not-affine-term

not-affine-bool : Bool
not-affine-bool = proj₁ is_affine

not-affine-is-affine-check : not-affine-bool ≡ true
not-affine-is-affine-check = refl


data AffineTerm : Set where
  var : (x : ℕ) → AffineTerm
  lam : (t : AffineTerm) → AffineTerm
  app : (t : AffineTerm) → (u : AffineTerm) → AffineTerm

data IsAffine : AffineTerm → Set where
  var : (x : ℕ) → IsAffine (var x)
  lam : (t : AffineTerm) → (p : IsAffine t) → IsAffine (lam t)
  app : (t : AffineTerm) → (u : AffineTerm) → (p₁ : IsAffine t) → (p₂ : IsAffine u) → IsAffine (app t u)

example : AffineTerm
example = lam (var 0)

example-is-affine : IsAffine example
example-is-affine = lam (var 0) (var 0)

