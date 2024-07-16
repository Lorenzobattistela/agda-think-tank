module selfTypes where

data Bool : Set where
  true : Bool
  false : Bool

-- type signature for the simple boolean type
bool : ∀ (A : Set) A → A → A
bool = _

-- type sig for if. Note that partially applying if results in the simple bool
if : ∀ (A : Set) Bool → A → A → A
if = _

a : Bool
a = true

-- type(if a) === ∀ (A : Set) A → A → A which is the same type as the simple bool

-- this is the type signature for a dependent match. It is also the eliminator for the inductive boolean
-- therefore, there should be a way for us to derive the inductive boolean type similarly to what we have done with the simple bool
match : ∀ {A : Set} (P : Bool → A) P true → P false → ∀ (b : Bool) → P b
match = _

-- not the syntax to define it in Agda, but this is the type for the inductive boolean
-- Note that it comes from partially applying the match too.
-- If we partially apply the match to a boolean b we would have
-- ∀ (P : Bool → A) P true → P false → P b
-- but we cant reference b here, and we know it is a boolean. But we are defining the boolean in this type?
-- So we need to reference ourselves! Thats why self is used
-- inducBool : ∀ {A : Set} ∀ self (P : Bool → A) P true → P false → P self

-- inductive def of naturals:
-- Nat : Type ∀ self(P : Nat -> Type) -> ∀(zero : P(λz. λs. z)) ->  ∀(succ : ∀(n : Nat) -> P (λz. λs. s n)) -> P self

data Nat : Set where
  zero : Nat
  succ : Nat → Nat

-- to define the induction principle for Nat, we take
-- a predicate P over nat
-- a proof that the predicate holds for zero
-- A function that given any n and a proof that P holds for n, produces a proof that P holds for succ n
-- A natural number n
-- And returns a proof that P holds for n
-- Basically the same as the induction principle for bools, but for nats

Nat-ind : (P : Nat → Set) → P zero → ((n : Nat) → P n → P (succ n)) → (n : Nat) → P n
Nat-ind P Pz Ps zero = Pz
Nat-ind P Pz Ps (succ n) = Ps n (Nat-ind P Pz Ps n)




