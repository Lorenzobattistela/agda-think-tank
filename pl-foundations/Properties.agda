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
progress (⊢μ ⊢M)      
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















































