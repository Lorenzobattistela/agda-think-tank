module pl-foundations.Properties where

open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; cong; cong₂)
open import Data.String using (String; _≟_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product
  using (_×_; proj₁; proj₂; ∃; ∃-syntax)
  renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Function using (_∘_)
open import logical-foundations.Isomorphism
open import pl-foundations.Lambda

-- ultimately, we would like to show that we can keep reducing a term until we reach a value. 
-- We might expect that every term is a value or can take a reduction step. But this property does not hold for every term, but it does for every closed, well-typed term
-- Progress: if ∅ ⊢ M ⦂ A , then either M is a value or there is an N such that M -> N
-- So either we have a value and we are done, or we can take a reduction step. In the latter, we would apply progress again. But to do so we need to know that the term yielded by the reduction is itself closed and well typed. This property will hold whenever we start with a closed well typed term
-- Preservation: if ∅ ⊢ M ⦂ A and M -> N then ∅ ⊢ N ⦂ A
-- Now we can automate evaluation. Start with a closed and well typed term. By progress, its either a value or we can reduce it further. By preservation, the other term will be well typed and closed. Repeat. We either will have non termination or eventually reach a value.


-- Values do not reduce
V¬—→ : ∀ {M N}
  → Value M
    ----------
  → ¬ (M —→ N)
V¬—→ V-ƛ        ()
V¬—→ V-zero     ()
V¬—→ (V-suc VM) (ξ-suc M—→N) = V¬—→ VM M—→N

-- we consider the three possibilities for values:
-- If it is an abbstraction then no reduction applies
-- same for zero
-- if it is a successor than e-suc may apply, but in that case the successor is itself of a value that reduces, which by induction cannot occur.
-- As a corollary, terms that reduce are not values.

—→¬V : ∀ {M N}
  → M —→ N
    ---------
  → ¬ Value M
—→¬V M—→N VM  =  V¬—→ VM M—→N

-- Progress: we would like to show that every term is either a value or takes a reduction step. However, this is not true in general. An example is zero ∙ suc zero
-- First, introduce a relation that captures what it means for a term M to make progress
data Progress (M : Term) : Set where
  step : ∀ {N}
    → M —→ N
      ----------
    → Progress M

  done :
      Value M
      ----------
    → Progress M
-- A term M makes progress if either it can take a step, meaning there exists a term N such that M -> N or if its done, meaning that M is a value.
-- If a term is well typed in the empty context then it satisfies progress:

progress : ∀ {M A}
  → ∅ ⊢ M ⦂ A
    ----------
  → Progress M
progress (⊢` ())
progress (⊢ƛ ⊢N)                            =  done V-ƛ
progress (⊢L · ⊢M) with progress ⊢L
... | step L—→L′                            =  step (ξ-·₁ L—→L′)
... | done V-ƛ with progress ⊢M
...   | step M—→M′                          =  step (ξ-·₂ V-ƛ M—→M′)
...   | done VM                             =  step (β-ƛ VM)
progress ⊢zero                              =  done V-zero
progress (⊢suc ⊢M) with progress ⊢M
...  | step M—→M′                           =  step (ξ-suc M—→M′)
...  | done VM                              =  done (V-suc VM)
progress (⊢case ⊢L ⊢M ⊢N) with progress ⊢L
... | step L—→L′                            =  step (ξ-case L—→L′)
... | done (V-zero)                         =  step β-zero
... | done (V-suc VL)                       =  step (β-suc VL)
progress (⊢μ ⊢M)                            =  step β-μ

-- we induct on the evidence that the term is well typed:
-- The term cannot be a variable, since no variable is well typed in the empty context
-- If the term is a lambda abstraction, then it is a value

-- If the term is an application L ∙ M, recursively apply progress to the derivation that L is well typed
-- Then, if the term steps, we have evidence that L -> L′, which by E-∙₁ means that our original term steps to L′ ∙ M
-- If the term is done, then we have evidence that L is a value, which must be a lambda abstraction
-- Recursively apply progress to the derivation that M is well typed:
-- If the term steps, we have evidence that M -> M′ which by E-∙₂ means that our original term stpes to L ∙ M′ . Step E-∙₂ applies only if we have evidence that L is a value, but progress on that subterm has already supplied the required evidence. If the term is done, we have evidence that M is a value, so our original term steps by β-ƛ 

-- The remaining cases are similar. if by induction we have a step case we apply a E rule, and if we have a done case either we have a value or apply a β rule. For fixpoint, no induction is required as the β rules applies immediately.
-- Our code reads neatly in part because we consider the step option before the done option. 

-- Prelude to preservation
-- The other property we wish to prove, preservation of typing under reduction requires more work.
-- The first step is to show that types are preserved by renaming 
-- Renaming: let Γ and Δ be two contexts such that every variable that appears in Γ also appears with the same type in Δ. Then if any term is typeable under Γ , it has the same type under Δ . In symbols:
-- ∀ {x A} → Γ ∋ x ⦂ A  →  Δ ∋ x ⦂ A
-- ---------------------------------
-- ∀ {M A} → Γ ⊢ M ⦂ A  →  Δ ⊢ M ⦂ A
--
-- Three important corollaries follow. The weaken lemma asserts that a term which is well typed in the empty context is also well typed in an arbitrary context. The drop lemma asserts that a term which is well typed in a context where the same variable appears twice remains well typed if we drop the shadowed occurrence.
-- The swap lemma asserts tha a term which is well typed in a context remains well typed if we swap two variables. 

-- The second step is to show that types are preserved by substitution
-- Substitution: say we have a closed term V of type A, and under the assumption that x has type A the term N has type B. Then substituting V for x in N yields a term that also has type B. In symbols:
-- ∅ ⊢ V ⦂ A
-- Γ , x ⦂ A ⊢ N ⦂ B
-- --------------------
-- Γ ⊢ N [ x := V ] ⦂ B

-- The result does not depend on V being a value, but it does require that V be closed. Recall that we restricted our attention to substitution by closed terms in order to avoid the need to rename bound variables. The term into which we are substituting is typed in an arbitrary context Γ, extended by the variable x for which we are substituting; and the result term is typed in Γ 
-- The lemma establishes that substitution composes well with typing: typing the components separately guarantees that the result of combining them is also well typed.
-- The third step is to show preservation.
-- Preservation: If ∅ ⊢ M ⦂ A and M -> N then ∅ ⊢ N ⦂ A
-- The proof is by induction over the possible reductions, and the substitution lemma is crucial in showing that each of the β rules that uses substitutions preserves types. 
--
-- Renaming:
-- We often need to "rebase" a type derivation, replacing a derivation Γ ⊢ M ⦂ A by a related derivation Γ ⊢ M ⦂A .
-- We may do so as long as every variable that appears in Γ also appears in Δ, and with the same type
-- Three of the rules for typing (lambda abstraction, case on naturals and fixpoint) have hypotheses that extend the context to include a bound variable. In each of these rules, Γ appears in the conclusion and Γ , x ⦂ A appears in the hypothesis. Thus:
-- Γ , x ⦂ A ⊢ N ⦂ B
-- ------------------- ⊢ƛ
-- Γ ⊢ ƛ x ⇒ N ⦂ A ⇒ B
-- For lambda expressions, and similarly for case and fixpoint. To deal with this situation, we first prove a lemma showing that if one context maps to another, this is still true after adding the same variable to both contexts.

ext : ∀ {Γ Δ}
  → (∀ {x A}     →         Γ ∋ x ⦂ A →         Δ ∋ x ⦂ A)
    -----------------------------------------------------
  → (∀ {x y A B} → Γ , y ⦂ B ∋ x ⦂ A → Δ , y ⦂ B ∋ x ⦂ A)
ext ρ Z           =  Z
ext ρ (S x≢y ∋x)  =  S x≢y (ρ ∋x)
-- let p be the name of the map that takes evidence that x appears in Γ to evidence that x appears in Δ 
-- The proof is by case analysis of the evidence that x appears in the extended context Γ , y ⦂ B:
--  If x is the same as y, we used Z to access the last variable in the extended Γ; and can similarly use Z to access the last variable in the extended Δ. 
--  If x differs from y, then we used S to skip over the last variable in the extended Γ where x≢y is evidence that x and y differ, and ∋x is the evidence that x appears in Γ ; and we can similarly use S to skip over the last variable in the extended Δ, applying p to find the evidence that x appears in Δ.
--  With the extension lemma, we can prove renaming preserves types:

rename : ∀ {Γ Δ}
  → (∀ {x A} → Γ ∋ x ⦂ A → Δ ∋ x ⦂ A)
    ----------------------------------
  → (∀ {M A} → Γ ⊢ M ⦂ A → Δ ⊢ M ⦂ A)
rename ρ (⊢` ∋w)    =  ⊢` (ρ ∋w)
rename ρ (⊢ƛ ⊢N)    =  ⊢ƛ (rename (ext ρ) ⊢N)
rename ρ (⊢L · ⊢M)  =  (rename ρ ⊢L) · (rename ρ ⊢M)
rename ρ ⊢zero      =  ⊢zero
rename ρ (⊢suc ⊢M)  =  ⊢suc (rename ρ ⊢M)
rename ρ (⊢case ⊢L ⊢M ⊢N)
                    =  ⊢case (rename ρ ⊢L) (rename ρ ⊢M) (rename (ext ρ) ⊢N)
rename ρ (⊢μ ⊢M)    =  ⊢μ (rename (ext ρ) ⊢M)
-- As before, let p be the name of the map that takes evidence that x appears in Γ to evidence that x appears in Δ. We induct on the evidence that M is well typed in Γ. Lets unpack the first three cases:
--  If the term is a variable, then applying p to the evidence that the variable appears in Γ yields the correpsonding evidence that the variable appears in Δ. 
--  If the term is a lambda abstraction, use the previous lemma to extend the map p suitably and use induction to rename the body of the abstraction
--  If the term is an application, use induction to rename both the function and the argument
-- The remaining cases are similar, inducting for each subterm and extending the map whenever the construct introduces a bound variable.
-- The induction is over the derivation that the term is well typed, so extending the context doesnt invalidate the inductive hypothesis. Equivalently, the recursion terminates because the second argument always grows smaller, even though the first argument sometimes grows larger. 
-- We have those three important corollaries, each proved by constructing a suitable map between contexts:
-- First: a closed term can be weakened to any context:
weaken : ∀ {Γ M A}
  → ∅ ⊢ M ⦂ A
    ----------
  → Γ ⊢ M ⦂ A
weaken {Γ} ⊢M = rename ρ ⊢M
  where
  ρ : ∀ {z C}
    → ∅ ∋ z ⦂ C
      ---------
    → Γ ∋ z ⦂ C
  ρ ()

-- here the map p is trivial, since there are no possible arguments in the empty context
-- Second, if the last two variables in a context are equal then we can drop the shadowed one:
drop : ∀ {Γ x M A B C}
  → Γ , x ⦂ A , x ⦂ B ⊢ M ⦂ C
    --------------------------
  → Γ , x ⦂ B ⊢ M ⦂ C
drop {Γ} {x} {M} {A} {B} {C} ⊢M = rename ρ ⊢M
  where
  ρ : ∀ {z C}
    → Γ , x ⦂ A , x ⦂ B ∋ z ⦂ C
      -------------------------
    → Γ , x ⦂ B ∋ z ⦂ C
  ρ Z                 =  Z
  ρ (S x≢x Z)         =  ⊥-elim (x≢x refl)
  ρ (S z≢x (S _ ∋z))  =  S z≢x ∋z
-- Here map p can never be invoked on the inner occurence of x since it is masked by the outer occurrence. Skipping over x in the first position can only happen if the variable looked for differs from x (the evidence for which is x≢x or z≢x) but if the variable is found in the second position, which also contains x, this leads to a contradiction (evidenced by x≢x refl).

-- Third, if the last two variables in a context differ then we can swap them
swap : ∀ {Γ x y M A B C}
  → x ≢ y
  → Γ , y ⦂ B , x ⦂ A ⊢ M ⦂ C
    --------------------------
  → Γ , x ⦂ A , y ⦂ B ⊢ M ⦂ C
swap {Γ} {x} {y} {M} {A} {B} {C} x≢y ⊢M = rename ρ ⊢M
  where
  ρ : ∀ {z C}
    → Γ , y ⦂ B , x ⦂ A ∋ z ⦂ C
      --------------------------
    → Γ , x ⦂ A , y ⦂ B ∋ z ⦂ C
  ρ Z                   =  S x≢y Z
  ρ (S z≢x Z)           =  Z
  ρ (S z≢x (S z≢y ∋z))  =  S z≢y (S z≢x ∋z)
-- Here the renaming map takes a variable at the end into a variable one from the end, and vice versa. The first line is responsible for moving x from a position at the end to a position one from the end with y at the end, and required the provided evidence that x≢y

-- Substitution
-- The key to preservation is the lemma establishing that substitution preserves types
-- In order to avoid renaming bound variables, substitution is restricted to be by closed terms only. This restriction was not enforced by our definition of substitution, but it is captured by our lemma to assert that substitution preserves typing.
-- The concern is with reducing closed terms, which means that when we apply β reduction, the term substituted in contains a single free variable (the bound variable of the lambda abstraction, or similarly for case or fixpoint). However, substitution is defined by recursion, and as we descend into terms with bound variables the context grows. So for the induction to go through, we require an arbitrary context Γ, as in the statement of the lemma.
-- Fromal statment and proof that substitution preserves types:
subst : ∀ {Γ x N V A B}
  → ∅ ⊢ V ⦂ A
  → Γ , x ⦂ A ⊢ N ⦂ B
    --------------------
  → Γ ⊢ N [ x := V ] ⦂ B
subst {x = y} ⊢V (⊢` {x = x} Z) with x ≟ y
... | yes _         =  weaken ⊢V
... | no  x≢y       =  ⊥-elim (x≢y refl)
subst {x = y} ⊢V (⊢` {x = x} (S x≢y ∋x)) with x ≟ y
... | yes refl      =  ⊥-elim (x≢y refl)
... | no  _         =  ⊢` ∋x
subst {x = y} ⊢V (⊢ƛ {x = x} ⊢N) with x ≟ y
... | yes refl      =  ⊢ƛ (drop ⊢N)
... | no  x≢y       =  ⊢ƛ (subst ⊢V (swap x≢y ⊢N))
subst ⊢V (⊢L · ⊢M)  =  (subst ⊢V ⊢L) · (subst ⊢V ⊢M)
subst ⊢V ⊢zero      =  ⊢zero
subst ⊢V (⊢suc ⊢M)  =  ⊢suc (subst ⊢V ⊢M)
subst {x = y} ⊢V (⊢case {x = x} ⊢L ⊢M ⊢N) with x ≟ y
... | yes refl      =  ⊢case (subst ⊢V ⊢L) (subst ⊢V ⊢M) (drop ⊢N)
... | no  x≢y       =  ⊢case (subst ⊢V ⊢L) (subst ⊢V ⊢M) (subst ⊢V (swap x≢y ⊢N))
subst {x = y} ⊢V (⊢μ {x = x} ⊢M) with x ≟ y
... | yes refl      =  ⊢μ (drop ⊢M)
... | no  x≢y       =  ⊢μ (subst ⊢V (swap x≢y ⊢M))
-- We induct on the evidence tha N is well typed in the context Γ extended by x
-- We note a issue with naming. In the lemma statement, the varialbe x is an implicit parameter for the variable substituted, while in the type rules for variables, abstractions, cases and fixpoints, the variable x is an implicit parameter for the relevant variable. We are going to need to get hold of both variables, so we use the syntax { x = y } to bind y to the substituted variable and the syntax { x = x } to bind x to the relevant variable in the patterns for ⊢′ , ⊢ƛ , ⊢case and ⊢μ . Using the name y here is consistent with the naming in the original definition of substitution in the previous chapter. The proof never mentions the types of x, y, V or N, so in what follows we choose type names as convenient.
-- Now what naming is resolved, we can unpack the first three cases: 
-- In the variable case, we must show:
-- ∅ ⊢ V ⦂ B
-- Γ , y ⦂ B ⊢ ` x ⦂ A
-- ------------------------
-- Γ ⊢ ` x [ y := V ] ⦂ A
-- Where the second hypothesis follows from
-- Γ , y ⦂ B ∋ x ⦂ A
-- There are two subcases, depending on the evidence for this judgement:

-- The lookup judgement is evidenced by rule Z:
-- ----------------
-- Γ , x ⦂ A ∋ x ⦂ A
-- In this case, x and y are necessarily identical, as are A and B. Nonetheless, we must evaluate x ≟ y in order to allow definition of substitution to simplify:
--  If the variables are equal, then after simplification we must show
--  ∅ ⊢ V ⦂ A
--  ---------
--  Γ ⊢ V ⦂ A
-- which follows by weakening
--  If the variables are unequal we have a contradiction

-- If the lookup judgement is evidenced by the rule S:
-- x ≢ y
-- Γ ∋ x ⦂ A
-- -----------
-- Γ , y ⦂ B ∋ x ⦂ A
-- in this case, x and y are necessarily distinct. Nonetheless, we must again evaluate x ≟ y in order to allow the definition of substitution to simplify:
--  If the variables are equal, we have a contradiction
--  If the variables are unequal, then after simplification we must show:
--  ∅ ⊢ V ⦂ B
--  x ≢ y
--  Γ ∋ x ⦂ A
--  -------------
--  Γ ⊢ ` x ⦂ A
--  which follows by the typing rule for variables

-- In the abstraction case, we must show:
-- ∅ ⊢ V ⦂ B
-- Γ , y ⦂ B ⊢ (ƛ x ⇒ N) ⦂ A ⇒ C
-- --------------------------------
-- Γ ⊢ (ƛ x ⇒ N) [ y := V ] ⦂ A ⇒ C
-- where the second hypothesis follows from:
-- Γ, y ⦂ B , x ⦂ A ⊢ N ⦂C
-- We evaluate x ≟ y in order to allow the definition of substitution to simplify:
--  If the variables are equal then after simplification we must show:
--  ∅ ⊢ V ⦂ B
--  Γ , x ⦂ B , x ⦂ A ⊢ N ⦂ C
--  -------------------------
--  Γ ⊢ ƛ x ⇒ N ⦂ A ⇒ C
--  From the drop lemma we know:
--  Γ , x ⦂ B , x ⦂ A ⊢ N ⦂ C
-- -------------------------
--  Γ , x ⦂ A ⊢ N ⦂ C
--  The ty0ping rule for abstraction then yields the required conclusion

--  If the variables are distinct then after simplification we must show:
--  ∅ ⊢ V ⦂ B
--  x ≢ y
--  Γ , y ⦂ B , x ⦂ A ⊢ N ⦂ C
--  --------------------------------
--  Γ ⊢ ƛ x ⇒ (N [ y := V ]) ⦂ A ⇒ C
--  from the swap lemma we know
--  x ≢ y
--  Γ , y ⦂ B , x ⦂ A ⊢ N ⦂ C
--  -------------------------
--  Γ , x ⦂ A , y ⦂ B ⊢ N ⦂ C
-- the inductive hypothesis gives:
--  ∅ ⊢ V ⦂ B
--  Γ , x ⦂ A , y ⦂ B ⊢ N ⦂ C
--  ----------------------------
--  Γ , x ⦂ A ⊢ N [ y := V ] ⦂ C
--  The typing rule for abstraction then yields the required conclusion
--
-- In the application case, we must show:
-- ∅ ⊢ V ⦂ C
-- Γ , y ⦂ C ⊢ L · M ⦂ B
-- --------------------------
-- Γ ⊢ (L · M) [ y := V ] ⦂ B
-- where the second hypothesis follows from the two judgements:
-- Γ , y ⦂ C ⊢ L ⦂ A ⇒ B
-- Γ , y ⦂ C ⊢ M ⦂ A
-- By the definition of substitution, we must show:
-- ∅ ⊢ V ⦂ C
-- Γ , y ⦂ C ⊢ L ⦂ A ⇒ B
-- Γ , y ⦂ C ⊢ M ⦂ A
-- ---------------------------------------
-- Γ ⊢ (L [ y := V ]) · (M [ y := V ]) ⦂ B
-- Applying the induction hypothesis for L and M and the typing rule for applications yields the required conclusion.

-- The remaining cases are similar, using induction for each subterm. Where the constructor introduces a bound variable, we need to compare it with the substituted variable, applying the drop lemma if they are equal and the swap lemma if they are distinct.

-- Preservation
-- Once we have shown that substitution preserves types, showing that reduction preserves types is straightforward

preserve : ∀ {M N A}
  → ∅ ⊢ M ⦂ A
  → M —→ N
    ----------
  → ∅ ⊢ N ⦂ A
preserve (⊢` ())
preserve (⊢ƛ ⊢N)                 ()
preserve (⊢L · ⊢M)               (ξ-·₁ L—→L′)     =  (preserve ⊢L L—→L′) · ⊢M
preserve (⊢L · ⊢M)               (ξ-·₂ VL M—→M′)  =  ⊢L · (preserve ⊢M M—→M′)
preserve ((⊢ƛ ⊢N) · ⊢V)          (β-ƛ VV)         =  subst ⊢V ⊢N
preserve ⊢zero                   ()
preserve (⊢suc ⊢M)               (ξ-suc M—→M′)    =  ⊢suc (preserve ⊢M M—→M′)
preserve (⊢case ⊢L ⊢M ⊢N)        (ξ-case L—→L′)   =  ⊢case (preserve ⊢L L—→L′) ⊢M ⊢N
preserve (⊢case ⊢zero ⊢M ⊢N)     (β-zero)         =  ⊢M
preserve (⊢case (⊢suc ⊢V) ⊢M ⊢N) (β-suc VV)       =  subst ⊢V ⊢N
preserve (⊢μ ⊢M)                 (β-μ)            =  subst (⊢μ ⊢M) ⊢M
-- the proof never mentions the types of M or N, so in what follows we choose type name as ocnvenient
-- Lets unpack the cases for two of the reduction rules:
-- Rule ξ-∙₁ we have:
-- L —→ L′
-- ----------------
-- L · M —→ L′ · M
-- where the left-hand side is typed by
-- Γ ⊢ L ⦂ A ⇒ B
-- Γ ⊢ M ⦂ A
-- -------------
-- Γ ⊢ L · M ⦂ B
-- By induction, we have
-- Γ ⊢ L ⦂ A ⇒ B
-- L —→ L′
-- --------------
-- Γ ⊢ L′ ⦂ A ⇒ B
-- from which the typing of the right-hand side follows immediately.
-- Rule β-ƛ. We have
-- Value V
-- -----------------------------
-- (ƛ x ⇒ N) · V —→ N [ x := V ]
-- where the left-hand side is typed by
-- Γ , x ⦂ A ⊢ N ⦂ B
-- -------------------
-- Γ ⊢ ƛ x ⇒ N ⦂ A ⇒ B    Γ ⊢ V ⦂ A
-- --------------------------------
-- Γ ⊢ (ƛ x ⇒ N) · V ⦂ B
-- By the substitution lemma, we have
-- Γ ⊢ V ⦂ A
-- Γ , x ⦂ A ⊢ N ⦂ B
-- --------------------
-- Γ ⊢ N [ x := V ] ⦂ B
-- from which the typing of the right-hand side follows immediately.
-- The remaining cases are similar. Each ξ rule follows by induction, and each β rule follows by the substitution lemma.

-- Evaluation
-- By repeated application of progress and preservation, we can evaluate any well typed term. 
-- Lets write an agda function that computes the reduction sequence from any given closed, well typed term to its value if it has one
-- Some terms may reduce forever, such as sucμ = μ "x" ⇒ `suc (`"x")
-- Since every agda computation must terminate (termination checker will complain), we cant simply ask agda to reduce a term to a value. Instead, we make it stop if it passes N reduction step. A good analogy is blockchain "gas" concept.

record Gas : Set where
  constructor gas
  field
    amount : ℕ
-- When our evaluator returns a term ℕ, it will either give evidence that N is a value or indicate that it ran out of gas:

data Finished (N : Term) : Set where
  done :
      Value N
      ----------
    → Finished N

  out-of-gas :
      ----------
      Finished N

-- Given a term L of type A, the evaluator will, for some N, return a reduction sequence from L to N and an indication of whether reduction finished:
data Steps (L : Term) : Set where
  steps : ∀ {N}
    → L —↠ N
    → Finished N
      ----------
    → Steps L

-- The evaluator takes gas and evidence that a term is well typed, and returns the corresponding steps:
eval : ∀ {L A}
  → Gas
  → ∅ ⊢ L ⦂ A
    ---------
  → Steps L
eval {L} (gas zero)    ⊢L                     =  steps (L ∎) out-of-gas
eval {L} (gas (suc m)) ⊢L with progress ⊢L
... | done VL                                 =  steps (L ∎) (done VL)
... | step {M} L—→M with eval (gas m) (preserve ⊢L L—→M)
...    | steps M—↠N fin                       =  steps (L —→⟨ L—→M ⟩ M—↠N) fin
-- let L be the name of the term we are reducing, and ⊢L be the evidence that L is well typed. We consider the amount of gas remaining. There are two possibilities:
-- It is zero, so we stop early. We return the trivial reduction L ->> L and an indication that we are out of gas
-- It is non-zero and after the next step we have m gas remaining. Apply progress to the evidence that term L is well typed. There are two possibilities:
--  Term L is a value, so we are done. We return the trivial reduction sequence L ->> L and the evidence that L is a value
--  Term L steps to another term M. Preservation provides evidence that M is also well typed, and we recursively invoke eval on the remaining gas. The result is evidence that M ->> N and indication of whether the reduction finished. We combine the evidence that L -> M and M ->> N to return evidence that L->> N and the indication of whether reduction finished.

-- Examples:
-- showing that it is well typed
⊢sucμ : ∅ ⊢ μ "x" ⇒ `suc ` "x" ⦂ `ℕ
⊢sucμ = ⊢μ (⊢suc (⊢` ∋x))
  where
  ∋x = Z

-- To show the first three steps of the infinite reduction sequence, we evaluate with three steps worth of gas:
_ : eval (gas 3) ⊢sucμ ≡
  steps
   (μ "x" ⇒ `suc ` "x"
   —→⟨ β-μ ⟩
    `suc (μ "x" ⇒ `suc ` "x")
   —→⟨ ξ-suc β-μ ⟩
    `suc (`suc (μ "x" ⇒ `suc ` "x"))
   —→⟨ ξ-suc (ξ-suc β-μ) ⟩
    `suc (`suc (`suc (μ "x" ⇒ `suc ` "x")))
   ∎)
   out-of-gas
_ = refl


-- Well typed terms dont get stuck
-- A term is normal if it cannot reduce:

Normal : Term → Set
Normal M = ∀ {N} → ¬ (M —→ N)

-- a term is stuck if it is normal yet not a value
Stuck : Term → Set
Stuck M = Normal M × ¬ Value M

-- using progress, it is easy to show that no well-typed term is stuck

postulate
  unstuck : ∀ {M A}
    → ∅ ⊢ M ⦂ A
      -----------
    → ¬ (Stuck M)

-- using preservation, it is easy to show that after any number of steps, a well-typed term remains well typed

postulate
  preserves : ∀ {M N A}
    → ∅ ⊢ M ⦂ A
    → M —↠ N
      ----------
    → ∅ ⊢ N ⦂ A

-- an easy consequence is that starting from a well typed term, taking any number of reduction steps leads to a term that is not stuck:
postulate
  wttdgs : ∀ {M N A}
    → ∅ ⊢ M ⦂ A
    → M —↠ N
      ------------
    → ¬ (Stuck N)

-- Felleisen and wright who introduce proof via progress and preservatoin, summarised this result with the slogan well-typed terms dont get stuck. 


-- Reduction is deterministic
-- When introduced reduction, there was a claim that it was deterministic. For completeness, now we shall present a formal proof.
-- We will need a variant of congruence to deal with functions of four arguments
cong₄ : ∀ {A B C D E : Set} (f : A → B → C → D → E)
  {s w : A} {t x : B} {u y : C} {v z : D}
  → s ≡ w → t ≡ x → u ≡ y → v ≡ z → f s t u v ≡ f w x y z
cong₄ f refl refl refl refl = refl

-- and now we can show that reduction is deterministic:
det : ∀ {M M′ M″}
  → (M —→ M′)
  → (M —→ M″)
    --------
  → M′ ≡ M″
det (ξ-·₁ L—→L′)   (ξ-·₁ L—→L″)     =  cong₂ _·_ (det L—→L′ L—→L″) refl
det (ξ-·₁ L—→L′)   (ξ-·₂ VL M—→M″)  =  ⊥-elim (V¬—→ VL L—→L′)
det (ξ-·₁ L—→L′)   (β-ƛ _)          =  ⊥-elim (V¬—→ V-ƛ L—→L′)
det (ξ-·₂ VL _)    (ξ-·₁ L—→L″)     =  ⊥-elim (V¬—→ VL L—→L″)
det (ξ-·₂ _ M—→M′) (ξ-·₂ _ M—→M″)   =  cong₂ _·_ refl (det M—→M′ M—→M″)
det (ξ-·₂ _ M—→M′) (β-ƛ VM)         =  ⊥-elim (V¬—→ VM M—→M′)
det (β-ƛ _)        (ξ-·₁ L—→L″)     =  ⊥-elim (V¬—→ V-ƛ L—→L″)
det (β-ƛ VM)       (ξ-·₂ _ M—→M″)   =  ⊥-elim (V¬—→ VM M—→M″)
det (β-ƛ _)        (β-ƛ _)          =  refl
det (ξ-suc M—→M′)  (ξ-suc M—→M″)    =  cong `suc_ (det M—→M′ M—→M″)
det (ξ-case L—→L′) (ξ-case L—→L″)   =  cong₄ case_[zero⇒_|suc_⇒_]
                                         (det L—→L′ L—→L″) refl refl refl
det (ξ-case L—→L′) β-zero           =  ⊥-elim (V¬—→ V-zero L—→L′)
det (ξ-case L—→L′) (β-suc VL)       =  ⊥-elim (V¬—→ (V-suc VL) L—→L′)
det β-zero         (ξ-case M—→M″)   =  ⊥-elim (V¬—→ V-zero M—→M″)
det β-zero         β-zero           =  refl
det (β-suc VL)     (ξ-case L—→L″)   =  ⊥-elim (V¬—→ (V-suc VL) L—→L″)
det (β-suc _)      (β-suc _)        =  refl
det β-μ            β-μ              =  refl
-- the proof is by induction over possible reductions. Considering three typical cases:
-- Two instances of ξ-·₁:
-- L —→ L′                 L —→ L″
-- --------------- ξ-·₁    --------------- ξ-·₁
-- L · M —→ L′ · M         L · M —→ L″ · M
-- By induction we have L′ ≡ L″, and hence by congruence L′ · M ≡ L″ · M.

-- An instance of ξ-·₁ and an instance of ξ-·₂:
                        -- Value L
-- L —→ L′                 M —→ M″
-- --------------- ξ-·₁    --------------- ξ-·₂
-- L · M —→ L′ · M         L · M —→ L · M″
-- The rule on the left requires L to reduce, but the rule on the right requires L to be a value. This is a contradiction since values do not reduce. If the value constraint was removed from ξ-·₂, or from one of the other reduction rules, then determinism would no longer hold.

-- Two instances of β-ƛ:

-- Value V                              Value V
-- ----------------------------- β-ƛ    ----------------------------- β-ƛ
-- (ƛ x ⇒ N) · V —→ N [ x := V ]        (ƛ x ⇒ N) · V —→ N [ x := V ]
-- Since the left-hand sides are identical, the right-hand sides are also identical. The formal proof simply invokes refl.

-- Five of the 18 lines in the above proof are redundant, e.g., the case when one rule is ξ-·₁ and the other is ξ-·₂ is considered twice, once with ξ-·₁ first and ξ-·₂ second, and the other time with the two swapped. What we might like to do is delete the redundant lines and add

-- det M—→M′ M—→M″ = sym (det M—→M″ M—→M′)
-- to the bottom of the proof. But this does not work: the termination checker complains, because the arguments have merely switched order and neither is smaller.
















