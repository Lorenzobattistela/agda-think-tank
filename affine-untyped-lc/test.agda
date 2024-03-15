module affine-untyped-lc.test where

open import Data.Bool using (if_then_else_; Bool; true; false; _∧_)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _≟_;_<_; _≤_)
open import Data.List using (List; _∷_; []; tail)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (Dec; yes; no)
open import Induction.WellFounded using (Acc; acc)
open import Data.Empty using (⊥; ⊥-elim)

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

contradiction : ∀ {A : Set} {x y : Bool} → x ≡ true → x ≡ false → A
contradiction refl ()

data Affine : Context → Term → Set where
  var : ∀ {ctx x} → lookup x ctx ≡ true → Affine ctx (var x)
  lam : ∀ {ctx t} → Affine (true ∷ ctx) t → Affine ctx (lam t)
  app : ∀ {ctx t u} → Affine ctx t → Affine (proj₂ (affine ctx t)) u → Affine ctx (app t u)

-- affine-implies-Affine : ∀ {ctx t} → proj₁ (affine ctx t) ≡ true → Affine ctx t
-- affine-implies-Affine {ctx} {var x} eq with lookup x ctx
-- ... | true = var refl
-- ... | false = contradiction eq refl


-- bound the size of the term by a natural number, show that β-reduction always strictly reduces the size of the term, and then do induction on the natural number bound to show termination.