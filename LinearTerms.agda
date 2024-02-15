module LinearTerms where

open import Data.Nat
open import Data.Bool

-- Define a datatype to represent variables
data Var : Set where
  V : N → Var

-- Define a datatype for terms with linearity
data Term : Set where
  var : Var → Term
  lam : (used : Bool) → Term → Term
  app : Term → Term → Term

-- Example terms
exampleTerm1 : Term
exampleTerm1 = lam true (var (V 0))

exampleTerm2 : Term
exampleTerm2 = lam false (app (var (V 0)) (var (V 1)))

exampleTerm3 : Term
exampleTerm3 = app (lam true (var (V 0))) (var (V 1))