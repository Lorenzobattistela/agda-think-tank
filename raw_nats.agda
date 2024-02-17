

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

a : Bool
a = true

b : Bool
b = true

equality_proof : a ≡ b
equality_proof = refl

ten : Nat
ten = 5 + 5

another_ten : Nat
another_ten = 2 * 5

eq_proof : ten ≡ another_ten
eq_proof = refl

data Bin : Set where
    <> : Bin
    _O : Bin → Bin
    _I : Bin → Bin

-- representing bitstring 1011
bitstring : Bin
bitstring = <> I O I I

-- inc <> I O I I ≡ <> I I O
inc : Bin → Bin
inc <> = <>
inc (x O) = x I
inc (x I) = inc(x) O

one_bitstring : Bin
one_bitstring = <> O I

two_bitsring : Bin
two_bitsring = <> I O

inc_one_bistring : Bin
inc_one_bistring = inc one_bitstring

eq_bin : inc_one_bistring ≡ two_bitsring
eq_bin = refl