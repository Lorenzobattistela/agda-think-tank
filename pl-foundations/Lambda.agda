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
-- but a single step is only part of the story. In general, we wish to repeatedly step a closed term until it reduces to a value.
-- We do this by defining the reflexive and transitive closure of the step relation. We define reflexive and transitive closure as a sequence of zero or more steps of the underlying relation.
infix  2 _—↠_
infix  1 begin_
infixr 2 _—→⟨_⟩_
infix  3 _∎

data _—↠_ : Term → Term → Set where
  _∎ : ∀ M
      ---------
    → M —↠ M

  step—→ : ∀ L {M N}
    → M —↠ N
    → L —→ M
      ---------
    → L —↠ N

pattern _—→⟨_⟩_ L L—→M M—↠N = step—→ L M—↠N L—→M

begin_ : ∀ {M N}
  → M —↠ N
    ------
  → M —↠ N
begin M—↠N = M—↠N

-- this can be read as follows:
-- From term M, we can take no steps, giving a step of type M -->> M. It is written M blackbox
-- From a term L we can take a single step of type L -> M followed by zero or more steps of type M ->> N, giving a step of type L ->> N. It is written L ->> ⟨ L -> M ⟩ M->>N where L->M and M->>N are steps of the appropriate type

-- Confluence: one important property a reduction relation might satisfy is to be confluent. If term L reduces to two other terms, M and N, then both of these reduce to a common term P. 
postulate
  confluence : ∀ {L M N}
    → ((L —↠ M) × (L —↠ N))
      --------------------
    → ∃[ P ] ((M —↠ P) × (N —↠ P))

  diamond : ∀ {L M N}
    → ((L —→ M) × (L —→ N))
      --------------------
    → ∃[ P ] ((M —↠ P) × (N —↠ P))

-- the reduction system studied in this chapter is deterministic, as in:
postulate
  deterministic : ∀ {L M N}
    → L —→ M
    → L —→ N
      ------
    → M ≡ N

-- it is easy to show that every deterministic relation satisfies the diamond and confluence properties. Hence, all the reduction systems studied are trivially confluent.
--
-- Example: The church numeral two applied to the suc and zero yields the nat number two.
_ : twoᶜ · sucᶜ · `zero —↠ `suc `suc `zero
_ =
  begin
    twoᶜ · sucᶜ · `zero
  —→⟨ ξ-·₁ (β-ƛ V-ƛ) ⟩
    (ƛ "z" ⇒ sucᶜ · (sucᶜ · ` "z")) · `zero
  —→⟨ β-ƛ V-zero ⟩
    sucᶜ · (sucᶜ · `zero)
  —→⟨ ξ-·₂ V-ƛ (β-ƛ V-zero) ⟩
    sucᶜ · `suc `zero
  —→⟨ β-ƛ (V-suc V-zero) ⟩
    `suc (`suc `zero)
  ∎

-- two plus two is four!
_ : plus · two · two —↠ `suc `suc `suc `suc `zero
_ =
  begin
    plus · two · two
  —→⟨ ξ-·₁ (ξ-·₁ β-μ) ⟩
    (ƛ "m" ⇒ ƛ "n" ⇒
      case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (plus · ` "m" · ` "n") ])
        · two · two
  —→⟨ ξ-·₁ (β-ƛ (V-suc (V-suc V-zero))) ⟩
    (ƛ "n" ⇒
      case two [zero⇒ ` "n" |suc "m" ⇒ `suc (plus · ` "m" · ` "n") ])
         · two
  —→⟨ β-ƛ (V-suc (V-suc V-zero)) ⟩
    case two [zero⇒ two |suc "m" ⇒ `suc (plus · ` "m" · two) ]
  —→⟨ β-suc (V-suc V-zero) ⟩
    `suc (plus · `suc `zero · two)
  —→⟨ ξ-suc (ξ-·₁ (ξ-·₁ β-μ)) ⟩
    `suc ((ƛ "m" ⇒ ƛ "n" ⇒
      case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (plus · ` "m" · ` "n") ])
        · `suc `zero · two)
  —→⟨ ξ-suc (ξ-·₁ (β-ƛ (V-suc V-zero))) ⟩
    `suc ((ƛ "n" ⇒
      case `suc `zero [zero⇒ ` "n" |suc "m" ⇒ `suc (plus · ` "m" · ` "n") ])
        · two)
  —→⟨ ξ-suc (β-ƛ (V-suc (V-suc V-zero))) ⟩
    `suc (case `suc `zero [zero⇒ two |suc "m" ⇒ `suc (plus · ` "m" · two) ])
  —→⟨ ξ-suc (β-suc V-zero) ⟩
    `suc `suc (plus · `zero · two)
  —→⟨ ξ-suc (ξ-suc (ξ-·₁ (ξ-·₁ β-μ))) ⟩
    `suc `suc ((ƛ "m" ⇒ ƛ "n" ⇒
      case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (plus · ` "m" · ` "n") ])
        · `zero · two)
  —→⟨ ξ-suc (ξ-suc (ξ-·₁ (β-ƛ V-zero))) ⟩
    `suc `suc ((ƛ "n" ⇒
      case `zero [zero⇒ ` "n" |suc "m" ⇒ `suc (plus · ` "m" · ` "n") ])
        · two)
  —→⟨ ξ-suc (ξ-suc (β-ƛ (V-suc (V-suc V-zero)))) ⟩
    `suc `suc (case `zero [zero⇒ two |suc "m" ⇒ `suc (plus · ` "m" · two) ])
  —→⟨ ξ-suc (ξ-suc β-zero) ⟩
    `suc (`suc (`suc (`suc `zero)))
  ∎

-- EXERCISE: one plus one is two






-- Syntax of Types
-- There are only two types: Functions, A => B and Naturals ‵ℕ (variants to avoid overlapping)

infixr 7 _⇒_

data Type : Set where
  _⇒_ : Type → Type → Type
  `ℕ : Type


-- Typing
-- Contexts
-- While reduction considers only closed terms, typing must consider terms with free variables. To type a term, we must first type its subterms, and in particular in the body of an abstraction its bound variable may appear free.
-- A context associates variables with types. we let Γ and Δ range over contexts. We write ∅ for the empty context, and Γ , X ⦂A for the context that extends Γ associating variable x with type A. For example:
-- ∅ , "S" ⦂ ‵ℕ ⇒ ‵ℕ , "z' ⦂ ‵ℕ is the context that associates variable "s" with type N -> N and variable z with type N
-- Contexts are formalised as follows:
--

infixl 5 _,_⦂_

data Context : Set where
  ∅ : Context
  _,_⦂_ : Context → Id → Type → Context

-- Lookup judgement
-- We have two forms of judgement. The first is written: Γ ∋ x ⦂ A and indicates in context Γ that variable x has type A. It is called lookup. Example:
-- ∅ , "s" ⦂ ‵ℕ ⇒ ‵ℕ , "z" ⦂ ‵ℕ ∋ "s" ⦂ ‵ℕ ⇒ ‵ℕ gives the type associated with variable "s"
-- If two variables in a contex have the same name, then lookup should return the most recently bound variable, which shadows the other variables. 

infix  4  _∋_⦂_

data _∋_⦂_ : Context → Id → Type → Set where

  Z : ∀ {Γ x A}
      ------------------
    → Γ , x ⦂ A ∋ x ⦂ A

  S : ∀ {Γ x y A B}
    → x ≢ y
    → Γ ∋ x ⦂ A
      ------------------
    → Γ , y ⦂ B ∋ x ⦂ A
-- the constructors Z and S correspond roughly to the constructors here and there for the element-of-relation _∈_ on lists. The constructor S takes an additional parameter, that ensures that when we look up a variable that it is not shadowed by another variable with the same name to its left in the list.
-- It can be tedious to use the S constructor because you have to provide proofs that x ≢ y each time. Example:

_ : ∅ , "x" ⦂ `ℕ ⇒ `ℕ , "y" ⦂ `ℕ , "z" ⦂ `ℕ ∋ "x" ⦂ `ℕ ⇒ `ℕ
_ = S (λ()) (S (λ()) Z)

-- instead, the use of a smart constructor that uses proof by refl to check the inequality while type checking is more convenient:
S′ : ∀ {Γ x y A B}
   → {x≢y : False (x ≟ y)}
   → Γ ∋ x ⦂ A
     ------------------
   → Γ , y ⦂ B ∋ x ⦂ A

S′ {x≢y = x≢y} x = S (toWitnessFalse x≢y) x

-- Typing judgmenet
-- The second judgement is written:
-- Γ ⊢ M ⦂ A and indicates in context Γ that term M has type A. Context Γ provides types for all the free variables in M.

infix  4  _⊢_⦂_

data _⊢_⦂_ : Context → Term → Type → Set where

  -- Axiom
  ⊢` : ∀ {Γ x A}
    → Γ ∋ x ⦂ A
      -----------
    → Γ ⊢ ` x ⦂ A

  -- ⇒-I
  ⊢ƛ : ∀ {Γ x N A B}
    → Γ , x ⦂ A ⊢ N ⦂ B
      -------------------
    → Γ ⊢ ƛ x ⇒ N ⦂ A ⇒ B

  -- ⇒-E
  _·_ : ∀ {Γ L M A B}
    → Γ ⊢ L ⦂ A ⇒ B
    → Γ ⊢ M ⦂ A
      -------------
    → Γ ⊢ L · M ⦂ B

  -- ℕ-I₁
  ⊢zero : ∀ {Γ}
      --------------
    → Γ ⊢ `zero ⦂ `ℕ

  -- ℕ-I₂
  ⊢suc : ∀ {Γ M}
    → Γ ⊢ M ⦂ `ℕ
      ---------------
    → Γ ⊢ `suc M ⦂ `ℕ

  -- ℕ-E
  ⊢case : ∀ {Γ L M x N A}
    → Γ ⊢ L ⦂ `ℕ
    → Γ ⊢ M ⦂ A
    → Γ , x ⦂ `ℕ ⊢ N ⦂ A
      -------------------------------------
    → Γ ⊢ case L [zero⇒ M |suc x ⇒ N ] ⦂ A

  ⊢μ : ∀ {Γ x M A}
    → Γ , x ⦂ A ⊢ M ⦂ A
      -----------------
    → Γ ⊢ μ x ⇒ M ⦂ A


-- Each type rule is named after the constructor for the corresponding term.
-- Most of the rules have a second name, derived from a convention in logic, whereby the rule is named after the type connective that it concerns; rules to introduce and to eliminate each connective are labeled -I and -E, respectively. As we read the rules from top to bottom, introduction and elimination rules do what they say on the tin: the first introduces a formula for the connective, which appears in the conclusion but not in the premises; while the second eliminates a formula for the connective, which appears in a premise but not in the conclusion. An introduction rule describes how to construct a value of the type (abstractions yield functions, successor and zero yield naturals), while an elimination rule describes how to deconstruct a value of the given type (applications use functions, case expressions use naturals).
-- Note also the three places (in ⊢ƛ, ⊢case, and ⊢μ) where the context is extended with x and an appropriate type, corresponding to the three places where a bound variable is introduced.
-- The rules are deterministic, in that at most one rule applies to every term.

-- Typings corresponding to computing two plus two:
⊢two : ∀ {Γ} → Γ ⊢ two ⦂ `ℕ
⊢two = ⊢suc (⊢suc ⊢zero)

⊢plus : ∀ {Γ} → Γ ⊢ plus ⦂ `ℕ ⇒ `ℕ ⇒ `ℕ
⊢plus = ⊢μ (⊢ƛ (⊢ƛ (⊢case (⊢` ∋m) (⊢` ∋n)
         (⊢suc (⊢` ∋+ · ⊢` ∋m′ · ⊢` ∋n′)))))
  where
  ∋+  = S′ (S′ (S′ Z))
  ∋m  = S′ Z
  ∋n  = Z
  ∋m′ = Z
  ∋n′ = S′ Z

⊢2+2 : ∅ ⊢ plus · two · two ⦂ `ℕ
⊢2+2 = ⊢plus · ⊢two · ⊢two


-- In contrast to our earlier examples, here we have typed two and plus in an arbitrary context rather than the empty context; this makes it easy to use them inside other binding contexts as well as at the top level. Here the two lookup judgments ∋m and ∋m′ refer to two different bindings of variables named "m". In contrast, the two judgments ∋n and ∋n′ both refer to the same binding of "n" but accessed in different contexts, the first where "n" is the last binding in the context, and the second after "m" is bound in the successor branch of the case.


-- Lookup is functional
-- The lookup relation is functional, in that for each Γ and x there is at most one A such that the judgement holds:
∋-functional : ∀ {Γ x A B} → Γ ∋ x ⦂ A → Γ ∋ x ⦂ B → A ≡ B
∋-functional Z        Z          =  refl
∋-functional Z        (S x≢ _)   =  ⊥-elim (x≢ refl)
∋-functional (S x≢ _) Z          =  ⊥-elim (x≢ refl)
∋-functional (S _ ∋x) (S _ ∋x′)  =  ∋-functional ∋x ∋x′


-- The typing relation Γ ⊢ M ⦂ A is not functional. For example, in any Γ the term ƛ "x" ⇒ ` "x" has type A ⇒ A for any type A.

-- Non examples:
-- We can also show that terms are not typeable. For example, here is a formal proof that it is not possible to type the term `zero · `suc `zero. It cannot be typed, because doing so requires that the first term in the application is both a natural and a function:

nope₁ : ∀ {A} → ¬ (∅ ⊢ `zero · `suc `zero ⦂ A)
nope₁ (() · _)


-- As a second example, here is a formal proof that it is not possible to type ƛ "x" ⇒ ` "x" · ` "x". It cannot be typed, because doing so requires types A and B such that A ⇒ B ≡ A:

nope₂ : ∀ {A} → ¬ (∅ ⊢ ƛ "x" ⇒ ` "x" · ` "x" ⦂ A)
nope₂ (⊢ƛ (⊢` ∋x · ⊢` ∋x′))  =  contradiction (∋-functional ∋x ∋x′)
  where
  contradiction : ∀ {A B} → ¬ (A ⇒ B ≡ A)
  contradiction ()
