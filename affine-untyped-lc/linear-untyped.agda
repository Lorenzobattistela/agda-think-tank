open import Data.Bool
open import Data.String
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Sum using (_⊎_) renaming (inj₁ to inl; inj₂ to inr)
open import Relation.Binary.PropositionalEquality

_>>=_ : ∀{a x y : Set} → a ⊎ x → (x → a ⊎ y) → a ⊎ y
inl x >>= f = inl x
inr y >>= f = f y

data UExpr : Set where
  UVar : String → UExpr
  ULam : String → UExpr → UExpr
  UApp : UExpr → UExpr → UExpr

module UScope where
  data Scope : Set where
    Empty : Scope
    _,_ : Scope → String → Scope

  _∈_ : String → Scope → Bool
  name ∈ Empty = false
  name ∈ (scope , name') = (name == name') ∨ (name ∈ scope)

data Error : Set where
  NotInScope : String → Error
  MultiUse : String → Error

checkLinearity : Scope → UExpr → Either Error ()
checkLinearity scope (UVar name) = 
  if name ∈ scope
  then Right ()
  else Left (NotInScope name)
checkLinearity scope (ULam name expr) = 
  checkLinearity (scope , name) expr
checkLinearity scope (UApp f x) = 
  checkLinearity scope f >>= λ _ → checkLinearity scope x


infixl 20 _∘_

module Ctx where
  data Ctx : Ty → Set where
    ◆ : Ctx I
    _,_ : ∀{a b} → Ctx a → String → Ctx (a ⊗ b)

  infixl 20 _,_

  _∈_ : ∀{a} → String → Ctx a → Bool
  name ∈ ◆ = false
  name ∈ (ctx , name') = (name == name') ∨ (name ∈ ctx)

open Ctx using (Ctx; ◆; _,_)

data Expr : Ty → Set where
  Var : String → (a : Ty) → Expr a
  Lam : ∀{b} → String → (a : Ty) → Expr b → Expr (a ⊸ b)
  App : ∀{a b} → Expr (a ⊸ b) → Expr a → Expr b


data Error : Set where
  NotInScope : String → Error
  UnusedVariable : String → Error
  DuplicateUse : String → Error
  TypeMismatch : String → (a b : Ty) → Error

case_of_ : ∀{a b : Set} → a → (a → b) → b
case_of_ x f = f x

record Compiled (b : Ty) : Set where
  constructor MkCompiled
  field
    inTy : Ty
    env : Ctx inTy
    arr : Arr inTy b

record UsedIn (a x' : Ty) : Set where
  constructor MkUsedIn
  field
    x : Ty
    ctx : Ctx x
    arr : Arr (x ⊗ a) x'

usedIn : ∀{y} → String → (a : Ty) → Ctx y → Error ⊎ (UsedIn a y)
usedIn name a ◆ = inl (UnusedVariable name)
usedIn {y = x ⊗ y} name a (ctx , name') =
  if name == name'
  then (
    case eqTy a y of λ{
      nothing → inl (TypeMismatch name a y);
      (just refl) → inr (MkUsedIn _ ctx id)
    }
  )
  else do
    (MkUsedIn _ ctx' arr) ← usedIn name a ctx
    inr (MkUsedIn _ (ctx' , name') (⟨ arr ⊗ id ⟩ ∘ assocl ∘ ⟨ id ⊗ swap ⟩ ∘ assocr))

record Merge (a b : Ty) : Set where
  constructor MkMerge
  field
    x : Ty
    ctx : Ctx x
    arr : Arr x (a ⊗ b)

merge : ∀{a b} → Ctx a → Ctx b → Error ⊎ Merge a b
merge ctxl ◆ = inr (MkMerge _ ctxl unitr)
merge ctxl (ctxr , name) =
  if name Ctx.∈ ctxl
  then inl (DuplicateUse name)
  else do
    (MkMerge _ ctx arr) ← merge ctxl ctxr
    inr (MkMerge _ (ctx , name) (assocr ∘ ⟨ arr ⊗ id ⟩))

module Scope where
  data Scope : Set where
    ◆ : Scope
    _,_ : Scope → String → Scope

  _∈_ : String → Scope → Bool
  name ∈ ◆ = false
  name ∈ (scope , name') = (name == name') ∨ (name ∈ scope)

open Scope using (Scope; ◆; _,_)

compile : ∀{b} → Scope → Expr b → Error ⊎ Compiled b
compile scope (Var name ty) =
  if name Scope.∈ scope
  then inr (MkCompiled (I ⊗ ty) (◆ , name) unitl⁻¹)
  else inl (NotInScope name)
compile scope (Lam name ty expr) = do
  (MkCompiled y ctx body') ← compile (scope , name) expr
  (MkUsedIn _ ctx' reassoc) ← usedIn name ty ctx
  inr (MkCompiled _ ctx' (abs (body' ∘ reassoc)))
compile scope (App f x) = do
  (MkCompiled _ ctxl f') ← compile scope f
  (MkCompiled _ ctxr x') ← compile scope x
  (MkMerge _ ctx split) ← merge ctxl ctxr
  inr (MkCompiled _ ctx (app ∘ ⟨ f' ⊗ x' ⟩ ∘ split))

test1 : ∀{a b} → Arr (a ⊗ b) (a ⊗ (I ⊗ b))
test1 =
  -- (a ⊗ (I ⊗ b))
  assocr ∘
  -- ((a ⊗ I) ⊗ b)
  ⟨ unitr ⊗ id ⟩
  -- (a ⊗ b)

test2 : ∀{a b} → Arr (a ⊗ b) (a ⊗ (I ⊗ b))
test2 =
  -- (a ⊗ (I ⊗ b))
  ⟨ id ⊗ unitl ⟩
  -- (a ⊗ b)

test3 :
  ∀{a a' b b' c c'} →
  Arr a a' →
  Arr b b' →
  Arr c c' →
  Arr (a ⊗ (b ⊗ c)) (a' ⊗ (b' ⊗ c'))
test3 f g h = assocr ∘ ⟨ ⟨ f ⊗ g ⟩ ⊗ h ⟩ ∘ assocl

test4 :
  ∀{a a' b b' c c'} →
  Arr a a' →
  Arr b b' →
  Arr c c' →
  Arr (a ⊗ (b ⊗ c)) (a' ⊗ (b' ⊗ c'))
test4 f g h = ⟨ f ⊗ ⟨ g ⊗ h ⟩ ⟩

test5 : ∀{a b} → Arr ((I ⊗ a) ⊗ b) (a ⊗ (I ⊗ b))
test5 = ⟨ unitl⁻¹ ⊗ unitl ⟩

optimise : ∀{a b} → Arr a b → Maybe (Arr a b)
optimise (unitl⁻¹ ∘ swap) = just unitr⁻¹
optimise (unitr⁻¹ ∘ swap) = just unitl⁻¹
optimise (assocr ∘ ⟨ unitr ⊗ id ⟩) = just ⟨ id ⊗ unitl ⟩
optimise (assocr ∘ ⟨ ⟨ f ⊗ g ⟩ ⊗ h ⟩ ∘ assocl) = just ⟨ f ⊗ ⟨ g ⊗ h ⟩ ⟩
optimise (x ∘ assocr ∘ ⟨ ⟨ f ⊗ g ⟩ ⊗ h ⟩ ∘ assocl) = just (x ∘ ⟨ f ⊗ ⟨ g ⊗ h ⟩ ⟩)
optimise _ = nothing
