module pl-foundations.Lambda where

open import Data.Bool using (Bool; true; false; T; not)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; _∷_; [])
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (∃-syntax; _×_)
open import Data.String using (String; _≟_)
open import Data.Unit using (tt)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Nullary.Decidable using (False; toWitnessFalse)
open import Relation.Nullary.Negation using (¬?)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)

-- syntax:
-- terms have seven constructs: 3 for the core lambda calculi
-- Variables: ‵ x
-- Abstractions ƛ x ⇒ N
-- Applications: L ∙ M
-- 3 for the naturals
-- Zero: ‵zero
-- successor ‵suc M
-- Case: case L [zero ⇒ M | suc x ⇒ N ]
-- And one for recursion:
-- Fixpoint μ x ⇒ M
-- With the exception of variables and fixpoints, each term form either constructs a value of a given type (abstractions yield functions, zero and successor yield natural numbers) or deconstructs it (applications use functions, case terms use naturals). We will see this again when we come to rules for assigning types to terms, where constructors correspond to introduction rules and deconstructors to eliminators
-- Syntax of terms in BNF:
-- L, M, N  ::=
-- ` x  |  ƛ x ⇒ N  |  L · M  |
-- `zero  |  `suc M  |  case L [zero⇒ M |suc x ⇒ N ]  |
-- μ x ⇒ M

Id : Set
Id = String

infix  5  ƛ_⇒_
infix  5  μ_⇒_
infixl 7  _·_
infix  8  `suc_
infix  9  `_

data Term : Set where
  `_                      :  Id → Term
  ƛ_⇒_                    :  Id → Term → Term
  _·_                     :  Term → Term → Term
  `zero                   :  Term
  `suc_                   :  Term → Term
  case_[zero⇒_|suc_⇒_]    :  Term → Term → Id → Term → Term
  μ_⇒_                    :  Id → Term → Term

-- identifiers are represented by string
-- Example term: nat two and plus functions:
two : Term
two = `suc `suc `zero

plus : Term
plus = μ "+" ⇒ ƛ "m" ⇒ ƛ "n" ⇒
         case ` "m"
           [zero⇒ ` "n"
           |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n") ]
-- the recursive definition of addition is similar to the original definition of _+_ for nats. Variable m is bound twice, once in the abstraction and onece in the suc branch of the case. The first use of m refers to the former and the second to the latter. ANy use ofm in the successor branch must refer to the latter binding, since the latter binding shadows the former. 
-- As a second example, its possible to use higher-order functions to represent natural numbers. In particular, the number n is represented by a function that accepts two arguments and applies the first n times to the second. This is the Church representation of the naturals:
twoᶜ : Term
twoᶜ =  ƛ "s" ⇒ ƛ "z" ⇒ ` "s" · (` "s" · ` "z")

-- λm.λn.λs.λz. (m s (n s z))
plusᶜ : Term
plusᶜ =  ƛ "m" ⇒ ƛ "n" ⇒ ƛ "s" ⇒ ƛ "z" ⇒
         ` "m" · ` "s" · (` "n" · ` "s" · ` "z")
sucᶜ : Term
sucᶜ = ƛ "n" ⇒ `suc (` "n")
-- the church numeral for two takes two args, s and z and applies s twice to z. Addition takes two numerals m and n, a function s and an argument z. It uses m to apply s to the result of using n to apply s to z. Hence, s is applied m plus n times to z. To convert a church numeral to the corresponding natural, we apply it to the sucᶜ function and the nat number zero.

mulᶜ : Term
mulᶜ = ƛ "m" ⇒ ƛ "n" ⇒ ƛ "s" ⇒ ƛ "z" ⇒
         ` "m" · (` "n" · ` "s") · ` "z"

-- another syntax for var:
-- T is a function that maps from the computation world to the evidence world, as defined in chapter Decidable
-- We ensure to use the primed functions only when the respective term argument is a variable, which we do by providing implicit evidence. For example, if we tried to define an abstraction term that binds anything but a variable:
-- _ : Term   _ = ƛ′ two ⇒ two   Agda would complain it cannot find a value of the bottom type for the implicit arg. The implicit arguments type reduces to ⊥ when term t is anything but a variable.
var? : (t : Term) → Bool
var? (` _)  =  true
var? _      =  false

ƛ′_⇒_ : (t : Term) → {_ : T (var? t)} → Term → Term
ƛ′_⇒_ (` x) N = ƛ x ⇒ N

case′_[zero⇒_|suc_⇒_] : Term → Term → (t : Term) → {_ : T (var? t)} → Term → Term
case′ L [zero⇒ M |suc (` x) ⇒ N ]  =  case L [zero⇒ M |suc x ⇒ N ]

μ′_⇒_ : (t : Term) → {_ : T (var? t)} → Term → Term
μ′ (` x) ⇒ N  =  μ x ⇒ N

-- now we can define plus as follows:
plus′ : Term
plus′ = μ′ + ⇒ ƛ′ m ⇒ ƛ′ n ⇒
          case′ m
            [zero⇒ n
            |suc m ⇒ `suc (+ · m · n) ]
  where
  +  =  ` "+"
  m  =  ` "m"
  n  =  ` "n"


-- In informal presentation of formal semantics, one uses choice of variable name to disambiguate and writes x rather than ` x for a term that is a variable. Agda requires we distinguish.

-- Similarly, informal presentation often use the same notation for function types, lambda abstraction, and function application in both the object language (the language one is describing) and the meta-language (the language in which the description is written), trusting readers can use context to distinguish the two. Agda is not quite so forgiving, so here we use ƛ x ⇒ N and L · M for the object language, as compared to λ x → N and L M in our meta-language, Agda.

-- bound and free variables:
-- A term with no free variables is closed, otherwise its open.

-- Values
-- A value is a term that corresponds to an answer. E.g, suc suc suc suc zero is a value, while plus ∙ two ∙ two is not. Following convention, we treat all function abstraction as values. This, plus by itself is considered a value. Value M holds if M is a value:

data Value : Term → Set where
  V-ƛ : ∀ {x N}
      --------------
    → Value (ƛ x ⇒ N)

  V-zero :
      --------------
      Value `zero

  V-suc : ∀ {V}
    → Value V
      --------------
    → Value (`suc V)

-- in informal presentations of formal semantics, using V as the name of a metavariable is sufficient to indicate that it is a value. In agda, we must explicitly invoke the Value predicate.
-- Another alternative is not to focus on closed terms, to treat variables as values and to treat ƛ x ⇒ N as a value only if N is a value. This is how agda normalises terms.


-- Substitution:
-- Is the heart of lambda calculus.
-- Substitututions are written as: N [ x := V ] which means "substitute term V for free occurrences of variable x in term N'
-- Substitution works if V is any closed term.
-- The definition of substitution presented here is only valid when the term substituted for the variable is closed
-- This is because substitution by terms that are not closed may require renaming of bound variables.

infix 9 _[_:=_]

_[_:=_] : Term → Id → Term → Term
-- if substituting in a variable, if the variable is eq to the term we want to substitue for, then do it. Else leave it as it is
(` x) [ y := V ] with x ≟ y  
... | yes _     = V
... | no _      = ` x

-- if substituting in a lambda abstraction, substitute the term inside if they are different (because if eq, x shadows y in the body N)
(ƛ x ⇒ N) [ y := V ] with x ≟ y
... | yes _     = ƛ x ⇒ N
... | no _      = ƛ x ⇒ N [ y := V ]

-- in the case of an application, we perform substitution recursively for the function and argument
(L · M) [ y := V ]  = L [ y := V ] · M [ y := V ]

-- for zero we dont need to substitute
(`zero) [ y := V ] = `zero

-- for suc again we recursively substitute after it
(`suc M) [ y := V ] = `suc M [ y := V ]

(case L [zero⇒ M |suc x ⇒ N ]) [ y := V ] with x ≟ y
... | yes _         = case L [ y := V ] [zero⇒ M [ y := V ] |suc x ⇒ N ]
... | no  _         = case L [ y := V ] [zero⇒ M [ y := V ] |suc x ⇒ N [ y := V ] ]

-- same shadowing reason, similar to lambda abs
(μ x ⇒ N) [ y := V ] with x ≟ y
... | yes _       = μ x ⇒ N
... | no _        = μ x ⇒ N [ y := V ]


-- Examples of substitutions:
_ : (ƛ "z" ⇒ ` "s" · (` "s" · ` "z")) [ "s" := sucᶜ ]
      ≡ ƛ "z" ⇒ sucᶜ · (sucᶜ · ` "z")
_ = refl

_ : (sucᶜ · (sucᶜ · ` "z")) [ "z" := `zero ] ≡ sucᶜ · (sucᶜ · `zero)
_ = refl

_ : (ƛ "x" ⇒ ` "y") [ "y" := `zero ] ≡ ƛ "x" ⇒ `zero
_ = refl

_ : (ƛ "x" ⇒ ` "x") [ "x" := `zero ] ≡ ƛ "x" ⇒ ` "x"
_ = refl

_ : (ƛ "y" ⇒ ` "y") [ "x" := `zero ] ≡ ƛ "y" ⇒ ` "y"
_ = refl


-- Reduction:
-- The reduction rules are for call-by-value lambda calculi. To reduce an application, we reduce left hand side untill it becomes a value (which must be an abstraction). Then reduce right hand side untill becomes a value. Then substitute the argument for the variable in the abstraction. E.g:
-- L —→ L′
-- --------------- ξ-·₁
-- L · M —→ L′ · M

-- M —→ M′
-- --------------- ξ-·₂
-- V · M —→ V · M′

-- ----------------------------- β-ƛ
-- (ƛ x ⇒ N) · V —→ N [ x := V ]

-- The rules break into two sorts. Compatibility rules direct us to reduce some part of a term. The names starts with the letter xi (ξ) . Once a term is sufficiently reduced, it will consist of a constructor and a deconstructor, in our case ƛ and ∙  which reduces directly. THey have name starting with beta (β) and are called beta rules.
-- A term that matches the left-hand side of a reduction rule is called a redex. In the redex (ƛ x ⇒ N) ∙ V , x can be referred as the formal parameter of the function and V as the actual parameter of the function application. Beta reduction replaces the formal parameter by the actual parameter. 
-- If a term is a value, no reduction applies. Conversely, if a reduction applies to a term then it is not a value. This exhausts the possibilities. Every well-typed term either reduces or it is a value.
--
-- For numbers, zero does not reduce and successor reduces the subterm. A case expression reduces its argument to a number, and then chooses the zero or succ branch as appropriate. A fixpoint replaces the bound variable by the entire fixpoint term; This is the one case where we substitute by a term that is not a value.

infix 4 _—→_

data _—→_ : Term → Term → Set where

  -- reduction on the left side of the fun app
  ξ-·₁ : ∀ {L L′ M}
    → L —→ L′
      -----------------
    → L · M —→ L′ · M

  -- reduction on the right side of app when left is already a value
  ξ-·₂ : ∀ {V M M′}
    → Value V
    → M —→ M′
      -----------------
    → V · M —→ V · M′

-- Beta reduction on abstractions
  β-ƛ : ∀ {x N V}
    → Value V
      ------------------------------
    → (ƛ x ⇒ N) · V —→ N [ x := V ]

  ξ-suc : ∀ {M M′}
    → M —→ M′
      ------------------
    → `suc M —→ `suc M′

  ξ-case : ∀ {x L L′ M N}
    → L —→ L′
      -----------------------------------------------------------------
    → case L [zero⇒ M |suc x ⇒ N ] —→ case L′ [zero⇒ M |suc x ⇒ N ]

  β-zero : ∀ {x M N}
      ----------------------------------------
    → case `zero [zero⇒ M |suc x ⇒ N ] —→ M

  β-suc : ∀ {x V M N}
    → Value V
      ---------------------------------------------------
    → case `suc V [zero⇒ M |suc x ⇒ N ] —→ N [ x := V ]

  β-μ : ∀ {x M}
      ------------------------------
    → μ x ⇒ M —→ M [ x := μ x ⇒ M ]

-- the reduction rules are designed to ensure that subterms of a term are reduced to values before the whole term is reduced. This is referred to as call-by-value reduction.
-- Further, the subterms are arranged in a way that they are reduced in a left-to-right order. This means that the reduction is deterministic. For any term, there is at most one other term to which it reduces. Our reduction relation is in fact a function.

-- Reflexive and transitive closure






