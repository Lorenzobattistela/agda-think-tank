open import Data.Bool using (Bool; true; false; T; not)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; _∷_; [])
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (∃-syntax; _×_)
open import Data.String using (String; _≟_)
open import Data.Unit using (tt)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Nullary.Decidable using (False; toWitnessFalse)
-- open import Relation.Nullary.Negation using (¬?)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)

-- terms syntax:
-- variables: `x
-- abstractions: ƛ x => N
-- applications: L @ M
-- naturals:
-- zero: `zero
-- succesor: `suc M
-- case: case L [zero => M | suc x => N]
-- one for recursion: fixpoint: μ x => M

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

-- example terms:
two : Term
two = `suc `suc `zero

one : Term
one = `suc `zero

plus : Term
plus = μ "+" ⇒ ƛ "m" ⇒ ƛ "n" ⇒
        case ` "n"
          [zero⇒ ` "n"
          |suc "m" ⇒ `suc(` "+" · ` "m" · ` "n") ]

-- mul = μ "*" ⇒ ƛ "m" ⇒ ƛ "n" ⇒ 
--         case ` "n"
--             [zero ⇒ `zero
--             |suc "n" ⇒ `"+" · ` "m" · (` "*" · ` "m" · "n")
--             ]

one_plus_one : Term
one_plus_one = plus · one · one

-- using higher order functions to represent nat numbers. In particular, the number n is represented by a function that accepts two args and applies the first n times to the second. This is church representation of naturals.

-- equivalent to: λs.λz s (s z)
twoᶜ : Term
twoᶜ =  ƛ "s" ⇒ ƛ "z" ⇒ ` "s" · (` "s" · ` "z")

-- equivalent to:
-- λm.λn.λs.λz. m s (n s z)
plusᶜ : Term
plusᶜ =  ƛ "m" ⇒ ƛ "n" ⇒ ƛ "s" ⇒ ƛ "z" ⇒
         ` "m" · ` "s" · (` "n" · ` "s" · ` "z")

-- λn. suc n
sucᶜ : Term
sucᶜ = ƛ "n" ⇒ `suc (` "n")

mulᶜ : Term
mulᶜ = ƛ "m" ⇒ ƛ "n" ⇒ ƛ "s" ⇒ ƛ "z"⇒ ` "m" · (` "n" · ` "s") · ` "z"


var? : (t : Term) → Bool
var? (` _)  =  true
var? _      =  false

ƛ′_⇒_ : (t : Term) → {_ : T (var? t)} → Term → Term
ƛ′_⇒_ (` x) N = ƛ x ⇒ N

case′_[zero⇒_|suc_⇒_] : Term → Term → (t : Term) → {_ : T (var? t)} → Term → Term
case′ L [zero⇒ M |suc (` x) ⇒ N ]  =  case L [zero⇒ M |suc x ⇒ N ]

μ′_⇒_ : (t : Term) → {_ : T (var? t)} → Term → Term
μ′ (` x) ⇒ N  =  μ x ⇒ N
-- Recall that T is a function that maps from the computation world to the evidence world, as defined in Chapter Decidable. We ensure to use the primed functions only when the respective term argument is a variable, which we do by providing implicit evidence.

-- _ : Term
-- _ = ƛ′ two ⇒ two
-- Agda would complain it cannot find a value of the bottom type for the implicit argument. Note the implicit argument’s type reduces to ⊥ when term t is anything but a variable.

plus′ : Term
plus′ = μ′ + ⇒ ƛ′ m ⇒ ƛ′ n ⇒
          case′ m
            [zero⇒ n
            |suc m ⇒ `suc (+ · m · n) ]
  where
  +  =  ` "+"
  m  =  ` "m"
  n  =  ` "n"


-- In an abstraction ƛ x ⇒ N we call x the bound variable and N the body of the abstraction. A central feature of lambda calculus is that consistent renaming of bound variables leaves the meaning of a term unchanged.

-- ƛ "s" ⇒ ƛ "z" ⇒ ` "s" · (` "s" · ` "z") has both s and z as bound variables.

-- ƛ "z" ⇒ ` "s" · (` "s" · ` "z") has z bound and s free.

-- ` "s" · (` "s" · ` "z") has both s and z as free variables.

-- We say that a term with no free variables is closed; otherwise it is open. Of the three terms above, the first is closed and the other two are open. We will focus on reduction of closed terms.

-- Different occurrences of a variable may be bound and free. In the term

-- (ƛ "x" ⇒ ` "x") · ` "x"
-- the inner occurrence of x is bound while the outer occurrence is free. By alpha renaming, the term above is equivalent to

-- (ƛ "y" ⇒ ` "y") · ` "x"
-- in which y is bound and x is free. A common convention, called the Barendregt convention, is to use alpha renaming to ensure that the bound variables in a term are distinct from the free variables, which can avoid confusions that may arise if bound and free variables have the same names.

-- case and recursion also introduce bound variables, which are subject to alpha renaming.

-- Values: a value is a term that corresponds to an answer
-- ex: `suc `suc zero is a value, while plus · two · two is not.
-- We treat all function abstractions as values. THus, plus itself is considered a value. The predicate Value M holds if term M is a value.

data Value : Term → Set where

  V-ƛ : ∀ {x N}
      ---------------
    → Value (ƛ x ⇒ N)

  V-zero :
      -----------
      Value `zero

  V-suc : ∀ {V}
    → Value V
      --------------
    → Value (`suc V)

-- An alternative is not to focus on closed terms, to treat variables as values, and to treat ƛ x ⇒ N as a value only if N is a value. Indeed, this is how Agda normalises terms. We consider this approach in Chapter Untyped.

-- substitution
-- We write substitution as N [ x := V ], meaning “substitute term V for free occurrences of variable x in term N”, or, more compactly, “substitute V for x in N”, or equivalently, “in N replace x by V”.
-- examples: (ƛ "z" ⇒ ` "s" · (` "s" · ` "z")) [ "s" := sucᶜ ] yields ƛ "z" ⇒ sucᶜ · (sucᶜ · ` "z").
-- (sucᶜ · (sucᶜ · ` "z")) [ "z" := `zero ] yields sucᶜ · (sucᶜ · `zero).
-- (ƛ "x" ⇒ ` "y") [ "y" := `zero ] yields ƛ "x" ⇒ `zero.

-- We will give a definition of substitution that is only valid when the term substituted for the variable is closed. This is because substitution by terms that are not closed may require renaming of bound variables. For example:

-- (ƛ "x" ⇒ ` "x" · ` "y") [ "y" := ` "x" · `zero] should not yield
-- (ƛ "x" ⇒ ` "x" · (` "x" · `zero)).
-- Instead, we should rename the bound variable to avoid capture:

-- (ƛ "x" ⇒ ` "x" · ` "y") [ "y" := ` "x" · `zero ] should yield
-- ƛ "x′" ⇒ ` "x′" · (` "x" · `zero).

infix 9 _[_:=_]
-- receives a term, an identifier and another term and returns a term
-- N [ x := V ] “substitute V for x in N”, or equivalently, “in N replace x by V”.
_[_:=_] : Term → Id → Term → Term
-- when the term is a variable, it checks if the variable matches the one to be substituted (x ≟ y). If yes, substitutes it with a V. If no, leave it unchanged.
(` x) [ y := V ] with x ≟ y
... | yes _         = V
... | no  _         = ` x
-- when the term is a lambda abstraction, chceks if the bound variable y matches the one to be substituted (v). If yes, it leaves the lambda unchanged because any occurence of x inside N is not free but bound to this lambda. If variables do not match, it substitutes x with V in the body N.
(ƛ x ⇒ N) [ y := V ] with x ≟ y
... | yes _         = ƛ x ⇒ N
... | no  _         = ƛ x ⇒ N [ y := V ]
-- when the term is an application, it substitutes V for x in both the function and the argument
(L · M) [ y := V ]  = L [ y := V ] · M [ y := V ]
-- when the term is zero, it does not substitute at all
(`zero) [ y := V ]  = `zero
-- when term is suc, it substitutes recursively the arg M
(`suc M) [ y := V ] = `suc M [ y := V ]
-- pattern matching case expressions: substitutes in the scrutinee L and both branches M and N. Specifically, it checks if x matches the variable bound in the successor case. If so, it does not substitute x in N, since x is bound in this case branch. Otherwise, proceeds with substitutions
(case L [zero⇒ M |suc x ⇒ N ]) [ y := V ] with x ≟ y
... | yes _         = case L [ y := V ] [zero⇒ M [ y := V ] |suc x ⇒ N ]
... | no  _         = case L [ y := V ] [zero⇒ M [ y := V ] |suc x ⇒ N [ y := V ] ]
-- fixedPoint operators: similar to lambda abstractions, it does not substitute within N if x is bound.
(μ x ⇒ N) [ y := V ] with x ≟ y
... | yes _         = μ x ⇒ N
... | no  _         = μ x ⇒ N [ y := V ]

-- example that examples above work
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

-- reduction
-- We give the reduction rules for call-by-value lambda calculus. To reduce an application, first we reduce the left-hand side until it becomes a value (which must be an abstraction); then we reduce the right-hand side until it becomes a value; and finally we substitute the argument for the variable in the abstraction.

-- In an informal presentation of the operational semantics, the rules for reduction of applications are written as follows:

-- L —→ L′
-- --------------- ξ-·₁
-- L · M —→ L′ · M

-- M —→ M′
-- --------------- ξ-·₂
-- V · M —→ V · M′

-- ----------------------------- β-ƛ
-- (ƛ x ⇒ N) · V —→ N [ x := V ]

-- Rules break into two sorts. Compatibility rules direct us to reduce some part of a term. We give them names starting with the greek letter ξ . Once a term is sufficiently reduced, it will consist of a constructor and a deconstructor, in our case ƛ and · which reduces directly. We give them names starting with the Greek letter β and such rules are called beta rules.
-- Terminology: a term that matches the left-hand side of a reduction rule is called a redex. In the redex (ƛ x ⇒ N) · V , we may refer to x as the formal parameter of the function, and V as the actual parameter of the function application. Beta reduction replaces the formal parameter by the actual parameter.
-- If a term is a value, no reduction applie. Conversely, if a reduction applies to a term then it is not a value. Every well-typed term either reduces or is a value.
-- For numbers, zero does not reduce and successor reduces the subterm. A case expression reduces its argument to a number, and chooses the zero or successor branch as appropriate. A fixpoint replaces the bound variable by the entire fixpoint term, being the one case where we substitute by a term that is not a value.

infix 4 _—→_

-- reduction receives two terms and returns a univ type set
data _—→_ : Term → Term → Set where
-- specify the reduction step of the left context of an application
-- here the constructor takes three args, L, L´ and M of type Term. They're implicit args, inferred by the agda type checker
  ξ-·₁ : ∀ {L L′ M}
    → L —→ L′
      -----------------
    → L · M —→ L′ · M -- the old application reduces to the reduced left side and untouched right side

-- same here, but now we reduce right side
  ξ-·₂ : ∀ {V M M′}
    → Value V
    → M —→ M′
      -----------------
    → V · M —→ V · M′

-- here we have beta reduction step, which reduces a lambda abstraction, taking x, N and V as args
  β-ƛ : ∀ {x N V}
  -- this premise specifies that V is a value. In lambda calc, a value is either an abstraction or var
    → Value V
      ------------------------------
      -- the conclusion states that if you have an application of the former form, where (ƛ x ⇒ N) represents a lambda abstraction, and V is a value, then you can reduce this
      -- expression to N with all occurences of x replaced by V.
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

-- Reduction rules are designed to ensure that subterms of a term are reduced to values before the whole term is reduced. This is referred to as call-by-value reduction.
-- Subterms are reduce in a left-to-right order, meaning that reduction is deterministic. For any term, there is at most one other term to which it reduces. Our reduction relation is in fact a function.

-- This style of explaining the meaning of terms is called a small-step operational semantics. If M —→ N, we say that term M reduces to term N, or equivalently, term M steps to term N. Each compatibility rule has another reduction rule in its premise; so a step always consists of a beta rule, possibly adjusted by zero or more compatibility rules.

-- Reflexive and Transitive Closure
-- in general, we want to repeateatedly step a closed term unitl it reduces to a value. We now define the reflexive and transitive closure of the step relation. We define reflexive and transitive closure as a sequence of zero or more steps of the underlying relation, along linems imilar to that for reasoning about chains of equalities.

infix  2 _—↠_
infix  1 begin_
infixr 2 _—→⟨_⟩_
infix  3 _∎

-- receives two terms and returns a set 
-- represents reduction steps
data _—↠_ : Term → Term → Set where
    -- from term M, we can take no steps, giving a step of type M —↠ M. Written M ∎.
    -- reflexive closure. The base case where no reduction steps are taken
  _∎ : ∀ M
      ---------
    → M —↠ M

-- step constructor: it takes three arguments
-- allows to construct a reduction step from L to N given that there is a reduction step from M to N and a term L can be reduced to N
-- essentially captures transitivity of reduction steps
  step—→ : ∀ L {M N}
    → M —↠ N
    → L —→ M
      ---------
    → L —↠ N

-- used for readability
pattern _—→⟨_⟩_ L L—→M M—↠N = step—→ L M—↠N L—→M

-- begin is a simple helper to begin proofs
begin_ : ∀ {M N}
  → M —↠ N
    ------
  → M —↠ N
begin M—↠N = M—↠N

-- Alternatively, we might define reflexive and transitive closure directly as the smallest relation that includes —→ and is reflexive and transitive. 

-- The three constructors specify, respectively, that —↠′ includes —→ and is reflexive and transitive. A good exercise is to show that the two definitions are equivalent (indeed, one embeds in the other).

data _—↠′_ : Term → Term → Set where

  step′ : ∀ {M N}
    → M —→ N
      -------
    → M —↠′ N

  refl′ : ∀ {M}
      -------
    → M —↠′ M

  trans′ : ∀ {L M N}
    → L —↠′ M
    → M —↠′ N
      -------
    → L —↠′ N


-- confluence
-- One important property a reduction relation might satisfy is to be confluent. If term L reduces to two other terms, M and N, then both of these reduce to a common term P.

postulate
  confluence : ∀ {L M N}
    → ((L —↠ M) × (L —↠ N))
      --------------------
    → ∃[ P ] ((M —↠ P) × (N —↠ P))

  diamond : ∀ {L M N}
    → ((L —→ M) × (L —→ N))
      --------------------
    → ∃[ P ] ((M —↠ P) × (N —↠ P))

postulate
  deterministic : ∀ {L M N}
    → L —→ M
    → L —→ N
      ------
    → M ≡ N

-- Examples:
-- The Church numeral two applied to the successor function and zero yields the natural number two:
_ : twoᶜ · sucᶜ · `zero —↠ `suc `suc `zero
_ =
  begin
  -- this is what we begin with
    twoᶜ · sucᶜ · `zero
  -- The ξ rule applies a reduction to the left side of an application when the right side is not yet reduced. Then, a beta reduction is applied within the context determined by ξ-·_1 . This beta reduction operates on a lambda abstraction and the lambda abstraction is a value. It unwraps the application of two to the suc function and translates it into the application of its definition to zero;
  —→⟨ ξ-·₁ (β-ƛ V-ƛ) ⟩
  -- λz.(suc · (suc · z) zero) -> result of the reduction
    (ƛ "z" ⇒ sucᶜ · (sucᶜ · ` "z")) · `zero
    -- here we have a beta rule that operates in a lambda abstraction and that it is a value zero. Basically it will substitute z for zero resulting in (suc (suc zero))
  —→⟨ β-ƛ V-zero ⟩
  -- result of the beta reduction
    sucᶜ · (sucᶜ · `zero)
    -- reduces the right side of the application where the left side is a lambda value. A beta reduction is applied within the context determined by the other rule (right side). The beta rule specifies that another beta reduction occurs in the right part of the expr, reducing it to suc suc zero.
  —→⟨ ξ-·₂ V-ƛ (β-ƛ V-zero) ⟩
  -- result of the reduction
    sucᶜ · `suc `zero
  —→⟨ β-ƛ (V-suc V-zero) ⟩ -- now we have another beta reduction that applies to the outermost application of the suc function. It identifies that the arg is itself a value obtained by applying the suc func to zero.
  -- nat num 2 as result
    `suc (`suc `zero)
  ∎



-- demonstrating that church numerals two plus two is four
_ : plusᶜ · twoᶜ · twoᶜ · sucᶜ · `zero —↠ `suc `suc `suc `suc `zero
_ =
  begin
  -- here we have our begin expression:
  -- @m.@n.@s.@z.(m s ( n  s  z )) two two suc zero
    (ƛ "m" ⇒ ƛ "n" ⇒ ƛ "s" ⇒ ƛ "z" ⇒ ` "m" · ` "s" · (` "n" · ` "s" · ` "z"))
      · twoᶜ · twoᶜ · sucᶜ · `zero
      -- at first, we reduce the left side (outtermost - m) in the context of recursively reducing the left side (which would be m n s) we have a beta reduction being applied to a lambda
  —→⟨ ξ-·₁ (ξ-·₁ (ξ-·₁ (β-ƛ V-ƛ))) ⟩
  -- the resulting expression is without @m and replaced all free occurences of m by two.
    (ƛ "n" ⇒ ƛ "s" ⇒ ƛ "z" ⇒ twoᶜ · ` "s" · (` "n" · ` "s" · ` "z"))
      · twoᶜ · sucᶜ · `zero
    -- we proceed further. The outermost rule is (left side) n. We do the same as before and reduce it.
  —→⟨ ξ-·₁ (ξ-·₁ (β-ƛ V-ƛ)) ⟩
  -- the resulting expression is: @s.@z(two s (two s z)) suc zero
    (ƛ "s" ⇒ ƛ "z" ⇒ twoᶜ · ` "s" · (twoᶜ · ` "s" · ` "z")) · sucᶜ · `zero
    -- continuing, we now will reduce the outermost left (s) and beta reduce it.
  —→⟨ ξ-·₁ (β-ƛ V-ƛ) ⟩
  -- the result is @z.(two suc (two suc z)) zero
    (ƛ "z" ⇒ twoᶜ · sucᶜ · (twoᶜ · sucᶜ · ` "z")) · `zero
    -- and finally we beta reduce our last part and expect a V-zero val
  —→⟨ β-ƛ V-zero ⟩
-- which results in two suc (two suc zero)
    twoᶜ · sucᶜ · (twoᶜ · sucᶜ · `zero)
    -- now again, we start by picking the outermost to reduce and apply beta reduction. This would give us the "raw" form of two and suc. (application).
  —→⟨ ξ-·₁ (β-ƛ V-ƛ) ⟩
-- the result is the lambda @z.(suc (suc z)) (two suc zero)
    (ƛ "z" ⇒ sucᶜ · (sucᶜ · ` "z")) · (twoᶜ · sucᶜ · `zero)

-- now we reduce the right side as well to get both on "raw" form.
  —→⟨ ξ-·₂ V-ƛ (ξ-·₁ (β-ƛ V-ƛ)) ⟩
  -- now we got: @z.(suc (suc z)) ((@z.(suc (suc z)) zero))
    (ƛ "z" ⇒ sucᶜ · (sucᶜ · ` "z")) · ((ƛ "z" ⇒ sucᶜ · (sucᶜ · ` "z")) · `zero)
    -- reducing the right side again. Applying beta reduction (we cant reduce more the left side)
  —→⟨ ξ-·₂ V-ƛ (β-ƛ V-zero) ⟩
  -- now we get: @z.(suc (suc z)) (suc (suc zero))
    (ƛ "z" ⇒ sucᶜ · (sucᶜ · ` "z")) · (sucᶜ · (sucᶜ · `zero))
    -- reducing right side twice. (reducing the application of suc to  zero (the innermost))
  —→⟨ ξ-·₂ V-ƛ (ξ-·₂ V-ƛ (β-ƛ V-zero)) ⟩
  -- now we reduce the other application of suc to suc zero
    (ƛ "z" ⇒ sucᶜ · (sucᶜ · ` "z")) · (sucᶜ · (`suc `zero))
    -- now we reduce again the right side, apply beta reduction and expect to get Vsuc Vzero
  —→⟨ ξ-·₂ V-ƛ (β-ƛ (V-suc V-zero)) ⟩
  -- now we get @z.(suc (suc z)) (suc suc zero)
    (ƛ "z" ⇒ sucᶜ · (sucᶜ · ` "z")) · (`suc `suc `zero)
    -- now we apply beta reduction on the expression
  —→⟨ β-ƛ (V-suc (V-suc V-zero)) ⟩
  -- result is @suc.(suc (suc suc zero))
    sucᶜ · (sucᶜ · `suc `suc `zero)
    -- now we reduce the right side since we cant reduce left side
  —→⟨ ξ-·₂ V-ƛ (β-ƛ (V-suc (V-suc V-zero))) ⟩
  -- and we get suc (suc suc suc zero)
    sucᶜ · (`suc `suc `suc `zero)
    -- now we beta reduce the last application
  —→⟨ β-ƛ (V-suc (V-suc (V-suc V-zero))) ⟩
  -- and we get suc suc suc suc zero which is incredibly FOUR
   `suc (`suc (`suc (`suc `zero)))
  ∎


-- reduction of one plus one = two
_ : plusᶜ · oneᶜ · oneᶜ · sucᶜ · `zero -↠ `suc `suc `zero
_ =
  begin
  -- begin expression:
  (ƛ "m" ⇒ ƛ "n" ⇒ ƛ "s" ⇒ ƛ "z" ⇒ `"m" · `"s" · (`"n" · `"s" · `"z"))  · oneᶜ · oneᶜ · sucᶜ · `zero 
  -- reducing left outermost m, n, and s. Beta reduction to lambda expressions
  —→⟨ ξ-·₁ (ξ-·₁ (ξ-·₁ (β—ƛ V—ƛ)))⟩
  -- result expr w m replaced
  (ƛ "n" ⇒ ƛ "s" ⇒ ƛ "z" ⇒ oneᶜ · `"s" · (`"n" · `"s" · `"z")) · oneᶜ · sucᶜ · `zero
  —→⟨ ξ-·₁ (ξ-·₁ (β—ƛ V—ƛ)) ⟩
  -- now reduce left side again, (n)
  -- result in:
  (ƛ "s" ⇒ ƛ "z" ⇒ oneᶜ · `"s" · (oneᶜ · `"s" · `"z")) · sucᶜ · `zero
  -- now lastly reducing s
  —→⟨ ξ-·₁ (β—ƛ V—ƛ) ⟩
  (ƛ "z" ⇒ oneᶜ · sucᶜ · (oneᶜ · sucᶜ · `"z")) · `zero
  -- lastly we beta reduce the z arg
  —→⟨ β—ƛ V—ƛ ⟩
  oneᶜ · sucᶜ · (oneᶜ · sucᶜ · `zero)
  -- now again we beta reduce the leftmost arg to get the definition of one
  -- @z.(suc z) (one suc zero)
  —→⟨ ξ-·₁ (β—ƛ V—ƛ) ⟩
  (ƛ "z" ⇒ sucᶜ · `"z") · (oneᶜ · sucᶜ · `zero)
  -- now we reduce the right side (left cannot be reduced more before that)
  —→⟨ ξ-·₂ V-ƛ (ξ-·₁ (β-ƛ V-ƛ)) ⟩
  -- @z.(suc z) @z.(suc z) zero
  -- this will reduce to @z.(suc z) suc zero
  -- and then suc suc zero = 2
  (ƛ "z" ⇒ sucᶜ · `"z") · (ƛ "z" ⇒ sucᶜ · `"z") · `zero
  -- reduce the application part on right side
  —→⟨ ξ-·₂ V-ƛ (β-ƛ V-zero) ⟩
  (ƛ "z" ⇒ sucᶜ · `"z") · sucᶜ · `zero
  -- now we will reduce the application of suc to zero
  —→⟨ ξ-·₂ V-ƛ (β-ƛ V-zero) ⟩
  (ƛ "z" ⇒ sucᶜ · `"z") · `suc `zero
  -- finally we apply beta reduction to the expr
  -- getting suc (suc zero)
  —→⟨ β-ƛ (V—suc (V—suc V-zero)) ⟩
  sucᶜ · `suc `zero
  —→⟨ β-ƛ (V—suc (V—suc V-zero)) ⟩
  -- now we need to beta reduce the application
  `suc (`suc `zero) -- which is = 2
-- syntax of types

-- for now he have just two types: function A=> B and Naturals, `ℕ

infixr 7 _⇒_

data Type : Set where
  _⇒_ : Type → Type → Type
  `ℕ : Type

-- precedence
-- functions of two or more args are represented via currying. This is made more convenient by declaring => to associate to the right and · to associate to the left. Thus:
-- (`ℕ ⇒ `ℕ) ⇒ `ℕ ⇒ `ℕ stands for ((`ℕ ⇒ `ℕ) ⇒ (`ℕ ⇒ `ℕ)).
-- plus · two · two stands for (plus · two) · two.

-- typing
-- Contexts
-- while reduction considers only closed terms, typing must consider terms with free variables. To type a term, we must first type its subterms, and in particular in the body of an abstraction its bound variable may appear free.
-- A context associates variables with types, we let Γ and Δ range over contexts. Write ∅ for the empty context, and Γ , x ⦂ A for the context that extends Γ by associating variable x with type A.

-- *************************************************************************** AFFINE TYPES **************************
-- infixl 5  _,_⦂_,_

-- data Usage : Set where
--   unused : Usage
--   used   : Usage

-- data Context : Set where
--   ∅     : Context
--   _,_⦂_,_ : Context → Id → Type → Usage → Context

-- infix  4  _∋_⦂_

-- data _∋_⦂_ : Context → Id → Type → Set where
--   -- Assuming linear types, we can only utilize 'Z' if the variable is 'unused'.
--   Z : ∀ {Γ x A}
--     → Γ , x ⦂ A , unused ∋ x ⦂ A

--   -- The 'S' rule is adapted to ensure that we track usage across different variables, without shadowing.
--   S : ∀ {Γ x y A B u}
--     → x ≢ y
--     → Γ ∋ x ⦂ A
--     → Γ , y ⦂ B , u ∋ x ⦂ A

-- updateUsage : Context → Id → Type → Context
-- updateUsage Γ x A = -- Implementation to mark x as 'used'

-- checkUnique : Context → Id → Bool
-- checkUnique Γ x = -- Implementation to check if 'x' is unique in 'Γ'
-- ****************************************************************************************************

data Context : Set where
  ∅     : Context
  _,_⦂_ : Context → Id → Type → Context

-- Lookup judgement
-- we have two forms of judgement. The first is writen:
-- Γ ∋ x ⦂ A

-- and indicates in context Γ that variable x has type A. It is called lookup. For example,

-- ∅ , "s" ⦂ `ℕ ⇒ `ℕ , "z" ⦂ `ℕ ∋ "z" ⦂ `ℕ
-- ∅ , "s" ⦂ `ℕ ⇒ `ℕ , "z" ⦂ `ℕ ∋ "s" ⦂ `ℕ ⇒ `ℕ
-- give us the types associated with variables "z" and "s", respectively. The symbol ∋ (pronounced “ni”, for “in” backwards) is chosen because checking that Γ ∋ x ⦂ A is analogous to checking whether x ⦂ A appears in a list corresponding to Γ.

-- If two variables in a context have the same name, then lookup should return the most recently bound variable, which shadows the other variables. For example,

-- ∅ , "x" ⦂ `ℕ ⇒ `ℕ , "x" ⦂ `ℕ ∋ "x" ⦂ `ℕ.
-- Here "x" ⦂ `ℕ ⇒ `ℕ is shadowed by "x" ⦂ `ℕ.
-- (IF WE WANTED TO MAKE TYPES LINEAR, WE COULD NOT DO SHADOWING, JUST DO NOT ALLOW IT)

infix  4  _∋_⦂_
-- represents a judgement that a var of a particular type exists within a context
-- "Within Context, there exists an identifier of Type."
data _∋_⦂_ : Context → Id → Type → Set where
-- Zero: used to assert that a new variable (and its type) is being added to the context. It operates under the assumption that the variable does not already exist in the context. The use of  {Γ x A} means these are implicit args. Agda infers them automatically. 
-- Γ , x ⦂ A ∋ x ⦂ A expression declares a new variable x of type A in the context Γ
  Z : ∀ {Γ x A}
      ------------------
    → Γ , x ⦂ A ∋ x ⦂ A

-- successor: this constructor asserts that if a variable x of type A exists in a context Γ , it still exists in the context after adding another variable y of type B assuming x ≢ y (not equiv to y). This implements shadowing.
  S : ∀ {Γ x y A B}
    → x ≢ y
    → Γ ∋ x ⦂ A
      ------------------
    → Γ , y ⦂ B ∋ x ⦂ A

-- to make this linear, we need a more rigorous check to be implemented to ensure a variable can not only not have the same name os another variable in the same context, but also must be "consumed" exactly once if its declared (in the case of affine, no need for once.)
-- It can be rather tedious to use the S constructor, as you have to provide proofs that x ≢ y each time. For example:

-- _ : ∅ , "x" ⦂ `ℕ ⇒ `ℕ , "y" ⦂ `ℕ , "z" ⦂ `ℕ ∋ "x" ⦂ `ℕ ⇒ `ℕ
-- _ = S (λ()) (S (λ()) Z)

-- Instead, we’ll use a “smart constructor”, which uses proof by reflection to check the inequality while type checking:
S′ : ∀ {Γ x y A B}
   → {x≢y : False (x ≟ y)}
   → Γ ∋ x ⦂ A
     ------------------
   → Γ , y ⦂ B ∋ x ⦂ A

S′ {x≢y = x≢y} x = S (toWitnessFalse x≢y) x

-- The second judgement is written: Γ ⊢ M ⦂ A and indicates in context Γ that term M has a type A. Cpntext provides types for all free variables in M. Example:
-- ∅ , "s" ⦂ `ℕ ⇒ `ℕ , "z" ⦂ `ℕ ⊢ ` "z" ⦂ `ℕ

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

