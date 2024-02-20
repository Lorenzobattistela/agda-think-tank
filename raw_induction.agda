
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


infix 1 begin_
infixr 2 _≡⟨⟩_
infix  3 _∎
infixl 6 _⊔_

postulate
  Level : Set

-- {-# BUILTIN LEVEL Level #-}

postulate
  lzero : Level
  lsuc  : (ℓ : Level) → Level
  _⊔_   : (ℓ₁ ℓ₂ : Level) → Level


{-# BUILTIN LEVELZERO lzero #-}
{-# BUILTIN LEVELSUC  lsuc  #-}
{-# BUILTIN LEVELMAX  _⊔_   #-}

private
  variable
    a b c ℓ ℓ₁ ℓ₂ ℓ₃ : Level
    A : Set a
    B : Set b
    C : Set c
  
REL : Set a → Set b → (ℓ : Level) → Set (a ⊔ b ⊔ suc ℓ)
REL A B ℓ = A → B → Set ℓ

Rel : Set a → (ℓ : Level) → Set (a ⊔ suc ℓ)
Rel A ℓ = REL A A ℓ

Trans : REL A B ℓ₁ → REL B C ℓ₂ → REL A C ℓ₃ → Set _
Trans P Q R = ∀ {i j k} → P i j → Q j k → R i k

Transitive : Rel A ℓ → Set _
Transitive _∼_ = Trans _∼_ _∼_ _∼_

-- if f is a fn from a to b, and x is equiv to y, f(x) should be equiv of f(y)
congruence : ∀ (f : A → B) { x y } → x ≡ y → f x ≡ f y
congruence f refl = refl

congruence' : ∀{f : A → B} x → f x ≡ f x
congruence' _ = refl

trans : Transitive {A = A} _≡_
trans refl eq = eq


-- for all values x and y of type a, given a proof that x is equal to y return a proof that x is equal to y. Used to 
-- begin equational reasoning
begin_ : ∀{x y : A} → x ≡ y → x ≡ y
begin_ x≡y = x≡y

-- here x is not an implicit parameter, just y, but essentially the same as begin
_≡⟨⟩_ : ∀ (x {y} : A) → x ≡ y → x ≡ y
_ ≡⟨⟩ x≡y = x≡y

step-≡ : ∀ (x {y z} : A) → y ≡ z → x ≡ y → x ≡ z
step-≡ _ y≡z x≡y = trans x≡y y≡z

syntax step-≡  x y≡z x≡y = x ≡⟨  x≡y ⟩ y≡z

_∎ : ∀ (x : A) → x ≡ x
_∎ _ = refl

-- proof of associativity
-- forall m n and p (there are nats)
-- returns a proof that (m + n) + p equivalent to m + (n + p)
+-associativity : ∀ (m n p : Nat) → (m + n) + p ≡ m + (n + p)

-- equational reasoning: for zero n and p, we know that zero + n + p should be equiv to n + p and therefore zero + (n + p)
-- 
+-associativity zero n p =
  begin
    (zero + n) + p
  ≡⟨⟩
    n + p
  ≡⟨⟩
    zero + (n + p)
  ∎
+-associativity (suc m) n p =
    begin
      (suc m + n) + p
    ≡⟨⟩
      suc(m + n) + p
    ≡⟨⟩
      suc((m + n) + p)
    ≡⟨ congruence suc (+-associativity m n p) ⟩
      suc (m + (n + p))
    ≡⟨⟩
      suc m + (n + p)
    ∎