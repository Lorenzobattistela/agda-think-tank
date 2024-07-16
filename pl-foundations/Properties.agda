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
-- Here the renaming map takes a variable at the end into a variable one from the end, and vice versa. The first line is responsible for moving x from a position at the end to a position one from the end with y at the end, and required the provided evidence that x≢y.

-- Substitution























































