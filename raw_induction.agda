
data Nat : Set where
    zero : Nat
    suc : (n : Nat) → Nat

{-# BUILTIN NATURAL Nat #-}

_+_ : Nat → Nat → Nat
zero + m = m 
suc n + m = suc(n + m)

-- example: 3 * 2 -> 2 + (2 * 2)
_*_ : Nat → Nat → Nat
zero * m = zero
(suc m) * n = n + (m * n) 


_-_ : Nat → Nat → Nat
n - zero = n
zero - (suc m) = zero
(suc m) - (suc n) = m - n

_^_ : Nat → Nat → Nat
m ^ zero = 1
m ^ (suc n) = m * (m ^ n)


data Bool : Set where
    false : Bool
    true : Bool

infix 4 _≡_
infixl 6  _+_  _-_
infixl 7  _*_

data _≡_ {a} {A : Set a} (x : A) : A → Set a where
  instance refl : x ≡ x


private 
    variable
        a b : Agda.Primitive.Level
        A B : Set a

-- Relation : Set a → (ℓ : Agda.Primitive.Level) → Set 

-- if f is a fn from a to b, and x is equiv to y, f(x) should be equiv of f(y)
congruence : ∀ (f : A → B) { x y } → x ≡ y → f x ≡ f y
congruence f refl = refl

congruence' : ∀{f : A → B} x → f x ≡ f x
congruence' _ = refl

-- symmetry : 

-- proof of associativity
+-associativity : ∀ (m n p : Nat) → (m + n) + p ≡ m + (n + p)
