module logical-foundations.Connectives where

-- propositions as types
-- conjunction is product
-- disjunction is sum
-- true is unit type
-- false is empty type
-- implication is function space

import Relation.Binary.PropositionalEquality as Eq
open Eq using(_≡_; refl)
open Eq.≡-Reasoning
open import Data.Nat using (ℕ)
open import Function using (_∘_)
open import logical-foundations.Isomorphism using (_≃_;_≲_; extensionality; _⇔_)
open logical-foundations.Isomorphism.≃-Reasoning

-- evidence that AxB holds is of the form (M, N) where M provides evidence for A and N for B
-- this is the same as the rules in proof theory and the same eliminations for logic (first order)
-- ⟨_,_⟩ on the left side is a constructor, its the introduction for conjunction
-- if we have it on the right side, its a destructor (or elimination)
-- how do we introduce connectives such as imply, or?
data _×_ (A B : Set) : Set where

  ⟨_,_⟩ :
      A
    → B
      -----
    → A × B

proj₁ : ∀ {A B : Set}
  → A × B
    ------
  → A

proj₁ ⟨ x , y ⟩ = x 

proj₂ : ∀ {A B : Set}
  → A × B
    ------
  → B

proj₂ ⟨ x , y ⟩ = y 

-- if we apply destructor and then reassemble with constructor, we have identity
-- for all A and B, if w is the conjunction of A and B, if we construct the destruction of w, it should be id!
η-× : ∀ {A B : Set} (w : A × B) → ⟨ proj₁ w , proj₂ w ⟩ ≡ w
η-× ⟨ x , y ⟩ = refl

-- binds less tightly than anything save disjunction
infixr 2 _×_ 

-- SYNTAX: we can also declare conjunction using records:
-- The difference is that for data types, we need to prove eta equality
-- for record types, eta equality holds by definition, so we do not need to pattern match on w
-- having eta equality definitionally can be quite convenient
record _×′_ (A B : Set) : Set where
  constructor ⟨_,_⟩′
  field
    proj₁′ : A
    proj₂′ : B
open _×′_

η-×′ : ∀ {A B : Set} (w : A ×′ B) → ⟨ proj₁′ w , proj₂′ w ⟩′ ≡ w
η-×′ w = refl

-- A x B is refered to as the product of A and B (or cartesian product with sets), and in computing it corresponds to a record type
-- Product type: if A has m distinct members and B has n distinct members, AxB has m*n distinct members:
data One : Set where
  one : One

data Two : Set where
  t1 : Two
  t2 : Two

-- 2 combinations
x-count : One × Two → ℕ
x-count ⟨ one , t1 ⟩ = 1
x-count ⟨ one , t2 ⟩ = 2

-- product on types also shares a property with prod on numbers in that there is a sense in which it is commutative
-- and associative. In particular, product is commutative and associative up to isomorphism.
-- for commutativity, the to function swaps a pair and the from does the same.
×-comm : ∀ {A B : Set} → A × B ≃ B × A
×-comm =
  record
  { to      = λ{ ⟨ x , y ⟩ → ⟨ y , x ⟩ }
  ; from    = λ{ ⟨ y , x ⟩ → ⟨ x , y ⟩ }
  ; from∘to = λ{ ⟨ x , y ⟩ → refl } --refl because if you apply to from you get id
  ; to∘from = λ{ ⟨ y , x ⟩ → refl }
  }
-- being commutative is differente from being commutative up to isomorphism. Compare:
-- m * n ≡ n * m | Here we might have m = 2 and n = 3, m*n = 6 n*m=6
-- A × B ≃ B × A | Here we might have A=One and n=Two, One×Two is not the same as Two×One
-- But there is an isomorphism between the two types. For instance, ⟨ one, t1 ⟩ which is a member of the former
-- corresponds to ⟨ t1 , one ⟩ which is a member of the latter

-- on associativity, we can have the following:
×-assoc : ∀ {A B C : Set} → (A × B) × C ≃ A × (B × C)
×-assoc =
  record
  { to      = λ{ ⟨ ⟨ x , y ⟩ , z ⟩  → ⟨ x , ⟨ y , z ⟩ ⟩ }
  ; from    = λ{ ⟨ x , ⟨ y , z ⟩ ⟩  → ⟨ ⟨ x , y ⟩ , z ⟩ }
  ; from∘to = λ{ ⟨ ⟨ x , y ⟩ , z ⟩  → refl } 
  ; to∘from = λ{ ⟨ x , ⟨ y , z ⟩ ⟩  → refl }
  }
-- being associative is not the same as being associative up to isomoprhism, same comparison as with comm
-- Exercise ⇔≃× show that A ⇔ B is isomorphic to (A → B) × (B → A)
-- isomorphism between two types means there are functions to convert back and forth between them, and these conversions are inverses of each other.
⇔-≃-× : ∀ {A B : Set } → A ⇔ B ≃ (A → B) × (B → A) 
⇔-≃-× =
  record
    { to = λ { record { to = A→B ; from = B→A } → ⟨ A→B , B→A ⟩ }
    ; from = λ { ⟨ A→B , B→A ⟩ → record { to = A→B ; from = B→A } }
    ; from∘to = λ { record { to = A→B ; from = B→A } → refl }
    ; to∘from = λ { ⟨ A→B , B→A ⟩ → refl }
    }


-- Truth is unit
-- truth always holds. Evidence that it holds is of the form tt
-- there is introduction rule but no elimination.
data ⊤ : Set where
  tt :
    --
    ⊤
 
-- replacing w by tt allows both sides of the prop equality to simplify to the same term
η-⊤ : ∀ (w : ⊤) → tt ≡ w
η-⊤ tt = refl
-- we can also declare truth as empty record
record ⊤′ : Set where
  constructor tt′
-- record {} corresponds to tt, constructor allows us to write tt′
truth′ : ⊤′
truth′ = _
-- we refer to it as unit type because it has only one member (tt)
-- for numbers, one is the id of mult. Correspondingly, unit is the id of product up to isomorphism
-- left identity
⊤-identityˡ : ∀ {A : Set} → ⊤ × A ≃ A
⊤-identityˡ =
  record
    { to      = λ{ ⟨ tt , x ⟩ → x }
    ; from    = λ{ x → ⟨ tt , x ⟩ }
    ; from∘to = λ{ ⟨ tt , x ⟩ → refl }
    ; to∘from = λ{ x → refl }
    }
-- id is diff from id up to isomoprhism, ⊤ × Bool is not the same as Bool, but there is isomorphism
-- right identity
-- use commutativity of × to prove right id
⊤-identityʳ : ∀ {A : Set} → A × ⊤ ≃ A
⊤-identityʳ{A} = 
  ≃-begin
    (A × ⊤)
  ≃⟨ ×-comm ⟩
    (⊤ × A)
  ≃⟨ ⊤-identityˡ ⟩
    A
  ≃-∎

-- disjunction is sum
-- same intro rules as logic we need either A or B providing evidence that A ⊎ B is true
data _⊎_ (A B : Set) : Set where
  inj₁ :
      A
      -----
    → A ⊎ B

  inj₂ :
      B
      -----
    → A ⊎ B
  
case-⊎ : ∀ {A B C : Set}
  → (A → C)
  → (B → C)
  → A ⊎ B
    -----------
  → C

-- we use inj as cons and destructors as well. inj introduces disjunction and case eliminates a disjunction
case-⊎ f g (inj₁ x) = f x
case-⊎ f g (inj₂ y) = g y

η-⊎ : ∀ {A B : Set} (w : A ⊎ B) → case-⊎ inj₁ inj₂ w  ≡ w
η-⊎ (inj₁ x) = refl
η-⊎ (inj₂ y) = refl


infixr 1 _⊎_
-- Thus, A × C ⊎ B × C parses as (A × C) ⊎ (B × C).

-- More generally, we can also throw in an arbitrary function from a disjunction:
uniq-⊎ : ∀ {A B C : Set} (h : A ⊎ B → C) (w : A ⊎ B) →
  case-⊎ (h ∘ inj₁) (h ∘ inj₂) w ≡ h w
uniq-⊎ h (inj₁ x) = refl
uniq-⊎ h (inj₂ y) = refl
-- its called the sum of A and B. In set theory, called the disjoint union and in computing it corresponds to a variant record type
⊎-count : One ⊎ Two → ℕ
⊎-count (inj₁ one) = 1
⊎-count (inj₂ t1) = 2
⊎-count (inj₂ t2) = 3
-- sum on types also shares a property with sum on numbers in that it is commutative and associative up to isomorphism

-- exercise commutativity of sum types
⊎-comm : ∀ {A B : Set} →  A ⊎ B ≃ B ⊎ A 
⊎-comm = 
  record
  { to      = λ{ (inj₁ x) → inj₂ x ; (inj₂ y) → inj₁ y }
  ; from    = λ{ (inj₁ y) → inj₂ y ; (inj₂ x) → inj₁ x }
  ; from∘to = λ{ (inj₁ x) → refl ; (inj₂ y) → refl } 
  ; to∘from = λ{ (inj₁ y) → refl ; (inj₂ x) → refl }
  }

-- exercise associativity of sum types
⊎-assoc : ∀ {A B C : Set} → (A ⊎ B) ⊎ C ≃ A ⊎ (B ⊎ C)
⊎-assoc = 
  record
  { to      = λ{ (inj₁ (inj₁ a)) → inj₁ a 
               ; (inj₁ (inj₂ b)) → inj₂ (inj₁ b)
               ; (inj₂ c) → inj₂ (inj₂ c)
               }
    ;
    from    = λ{ (inj₁ a) → inj₁ (inj₁ a)
               ; (inj₂ (inj₁ b)) → inj₁ (inj₂ b) 
               ; (inj₂ (inj₂ c)) → (inj₂ c)
               } 
    ;
    from∘to = λ{ (inj₁ (inj₁ a)) → refl
               ; (inj₁ (inj₂ a)) → refl
               ; (inj₂ a) → refl
               }
    ;
    to∘from = λ{ (inj₁ a) → refl
               ; (inj₂ (inj₁ a)) → refl
               ; (inj₂ (inj₂ a)) → refl
               }
  }


-- false
-- same as fo logic
data ⊥ : Set where
-- empty

⊥-elim : ∀ {A : Set}
  → ⊥
    --
  → A
⊥-elim () -- absurd
-- ⊥ has 0 members

-- no value can match our type ⊥
-- id of sum up to isomorph
uniq-⊥ : ∀ {C : Set} (h : ⊥ → C) (w : ⊥) → ⊥-elim w ≡ h w
uniq-⊥ h ()

-- exerc: ⊥-identityˡ
⊥-identityˡ : ∀ {A : Set} → ⊥ ⊎ A ≃ A
⊥-identityˡ =
  record
    { to      = λ{ (inj₂ x) → x }
    ; from    = λ{ x → inj₂ x } 
    ; from∘to = λ{ (inj₂ x) → refl }
    ; to∘from = λ{ x → refl}
    }

⊥-identityʳ : ∀ {A : Set} → A ⊎ ⊥ ≃ A
⊥-identityʳ {A} = 
  ≃-begin
    (A ⊎ ⊥)
  ≃⟨ ⊎-comm ⟩
    (⊥ ⊎ A)
  ≃⟨ ⊥-identityˡ ⟩
    A
  ≃-∎

-- implication is function
-- evidence that A → B holds: λ (x : A) → N where N : B containing x as free var
-- same elim rule as in logic (APP)
→-elim : ∀ {A B : Set}
  → (A → B)
  → A
    -----
  → B
→-elim L M = L M

-- introduction coms at the form:
-- λ (x : A) → N

η-→ : ∀ {A B : Set} (f : A → B) → (λ (x : A) → f x) ≡ f
η-→ f = refl
-- if type A has N members and type B has M members A → B has n^m members
-- (p ^ n) ^ m ≡ p ^ (n * m)
-- A → (B → C) ≃ (A × B) → C this is currying

currying : ∀{A B C : Set} → (A → B → C) ≃ (A × B → C)
currying =
  record
  { to      = λ{ f → λ{ ⟨ x , y ⟩ → f x y } }
  ; from    = λ{ g → λ{ x → λ{ y → g ⟨ x , y ⟩ } } }
  ; from∘to = λ{ f → refl }
  ; to∘from = λ{ g → extensionality λ{ ⟨ x , y ⟩ → refl } }
  }

-- p ^ (n + m) = (p ^ n) * (p ^ m)
-- (A ⊎ B) → C ≃ (A → C) × (B → C)
→-distrib-⊎ : ∀ {A B C : Set } → (A ⊎ B → C) ≃ ((A → C) × (B → C))
→-distrib-⊎ = 
  record
  { to        = λ{ f → ⟨ f ∘ inj₁ , f ∘ inj₂ ⟩ }
  ; from      = λ{ ⟨ g , h ⟩ → λ{ (inj₁ x) → g x ; (inj₂ y) → h y } }
  ; from∘to   = λ{ f → extensionality λ{ (inj₁ x) → refl ; (inj₂ y) → refl } }
  ; to∘from   = λ{ ⟨ g , h ⟩ → refl }
  }

-- we can also do (p * n) ^ m = (p ^ m) * (n ^ m)
-- A → B × C ≃ (A → B) × (A → C)
→-distrib-× : ∀ {A B C : Set } → (A → B × C) ≃ ((A → B) × (A → C))
→-distrib-× = 
  record
  { to        = λ{ f → ⟨ proj₁ ∘ f , proj₂ ∘ f ⟩ }
  ; from      = λ{ ⟨ g , h ⟩ → λ x → ⟨ g x , h x ⟩ }
  ; from∘to   = λ{ f → extensionality λ{ x → η-× (f x) } }
  ; to∘from   = λ{ ⟨ g , h ⟩ → refl }
  }

-- also define product distribution over sum
×-distrib-⊎ : ∀ {A B C : Set } → (A ⊎ B) × C ≃ (A × C) ⊎ (B × C)
×-distrib-⊎ = 
  record
  { to        = λ{ ⟨ inj₁ x , z ⟩ → (inj₁ ⟨ x , z ⟩)
                 ; ⟨ inj₂ y , z ⟩ → (inj₂ ⟨ y , z ⟩)
                 }
  ; from      = λ{ (inj₁ ⟨ x , z ⟩) → ⟨ inj₁ x , z ⟩
                 ; (inj₂ ⟨ y , z ⟩) → ⟨ inj₂ y , z ⟩
                 }
  ; from∘to   = λ{ ⟨ inj₁ x , z ⟩ → refl
                 ; ⟨ inj₂ y , z ⟩ → refl
                 }
  ; to∘from   = λ{ (inj₁ ⟨ x , z ⟩) → refl
                 ; (inj₂ ⟨ y , z ⟩) → refl
                 }
  }


⊎-distrib-× : ∀ {A B C : Set} → (A × B) ⊎ C ≲ (A ⊎ C) × (B ⊎ C)
⊎-distrib-× =
  record
    { to      = λ{ (inj₁ ⟨ x , y ⟩) → ⟨ inj₁ x , inj₁ y ⟩
                 ; (inj₂ z)         → ⟨ inj₂ z , inj₂ z ⟩
                 }
    ; from    = λ{ ⟨ inj₁ x , inj₁ y ⟩ → (inj₁ ⟨ x , y ⟩)
                 ; ⟨ inj₁ x , inj₂ z ⟩ → (inj₂ z)
                 ; ⟨ inj₂ z , _      ⟩ → (inj₂ z)
                 }
    ; from∘to = λ{ (inj₁ ⟨ x , y ⟩) → refl
                 ; (inj₂ z)         → refl
                 }
    }




























