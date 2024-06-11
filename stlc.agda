open import Agda.Builtin.String
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_)

data Type : Set where
  ty-bool : Type
  ty-abs  : Type → Type → Type

data Ctx : Set  where
  ∅ : Ctx
  _↪_::_ : String → Type → Ctx →  Ctx

data Weak : Ctx → String → Type → Ctx → Set where
  weak : ∀ Γ x τ → Weak Γ x τ (x ↪ τ :: Γ)

data Weak-n : Ctx → Ctx → Set  where
  weak-n-base : ∀ Γ x τ
    → Weak Γ x τ(x ↪ τ :: Γ)
    → Weak-n Γ (x ↪ τ :: Γ)
  weak-n-symm : ∀ Γ
    → Weak-n Γ Γ
  weak-n-trans : ∀ Γ Γ' Γ''
    → Weak-n Γ Γ'
    → Weak-n Γ' Γ''
    → Weak-n Γ Γ''

data Term : Set where
  tm-true  : Term
  tm-false : Term
  tm-var   : String →  Term
  tm-abs   : String → Type → Term → Term
  tm-app   : Term → Term → Term
  tm-if    : Term → Term → Term → Term

data _[_/_]⇛_ : Term → Term → String → Term → Set where
  subst-true : ∀ x eₓ
    → tm-true [ eₓ / x ]⇛ tm-true
  subst-false : ∀ x eₓ
    → tm-false [ eₓ / x ]⇛ tm-false
  subst-var-eq : ∀ x eₓ
    → (tm-var x) [ eₓ / x ]⇛ eₓ
  subst-var-ne : ∀ x eₓ y
    → (tm-var y) [ eₓ / x ]⇛ (tm-var y)
  subst-if : ∀ x eₓ e₁ e₂ e₃ e₁' e₂' e₃'
    → e₁ [ eₓ / x ]⇛ e₁'
    → e₂ [ eₓ / x ]⇛ e₂'
    → e₃ [ eₓ / x ]⇛ e₃'
    → (tm-if e₁ e₂ e₃) [ eₓ / x ]⇛ (tm-if e₁' e₂' e₃')
  subst-abs : ∀ x eₓ y τ e e'
    → e [ eₓ / x ]⇛ e'
    → (tm-abs y τ e) [ eₓ / x ]⇛ (tm-abs y τ e')
  subst-app : ∀ x eₓ e₁ e₂ e₁' e₂'
    → e₁ [ eₓ / x ]⇛ e₁'
    → e₂ [ eₓ / x ]⇛ e₂'
    → (tm-app e₁ e₂) [ eₓ / x ]⇛ (tm-app e₁' e₂') 

data _↪_∈_ : String → Type → Ctx → Set where
  ∈-b : ∀ x τ Γ
    → x ↪ τ ∈ (x ↪ τ :: Γ)
  ∈-i : ∀ x τ x' τ' Γ
    → x ≢ x'
    → x ↪ τ ∈ Γ
    → x ↪ τ ∈ (x' ↪ τ' :: Γ)

data _∉_ : String → Ctx → Set where
  ∉-b : ∀ x
    → x ∉ ∅
  ∉-i : ∀ x Γ y τ
    → x ≢ y
    → x ∉ Γ
    → x ∉ (y ↪ τ :: Γ)

data _⊢_∶_ : Ctx → Term → Type → Set where
  t-true : ∀ Γ
    → Γ ⊢ tm-true ∶ ty-bool
  t-false : ∀ Γ
    → Γ ⊢ tm-false ∶ ty-bool
  t-var : ∀ Γ x τ
    → x ↪ τ ∈ Γ
    → Γ ⊢ tm-var x ∶ τ
  t-if : ∀ Γ τ e₁ e₂ e₃
    → Γ ⊢ e₁ ∶ ty-bool
    → Γ ⊢ e₂ ∶ τ
    → Γ ⊢ e₃ ∶ τ
    → Γ ⊢ tm-if e₁ e₂ e₃ ∶ τ
  t-abs : ∀ Γ x τ₁ τ₂ e
    → (x ↪ τ₁ :: Γ) ⊢ e ∶ τ₂
    → Γ ⊢ tm-abs x τ₁ e ∶ ty-abs τ₁ τ₂
  t-app : ∀ Γ e₁ e₂ τ₁ τ₂
    → Γ ⊢ e₁ ∶ ty-abs τ₁ τ₂
    → Γ ⊢ e₂ ∶ τ₂
    → Γ ⊢ tm-app e₁ e₂ ∶ τ₂

data Value : Term → Set where
  v-true  : Value tm-true
  v-false : Value tm-false
  v-abs   : ∀ x τ e → Value (tm-abs x τ e)

data _↦_ : Term → Term → Set where
  s-if-true : ∀ e₁ e₂
    → tm-if tm-true e₁ e₂ ↦ e₁
  s-if-false : ∀ e₁ e₂
    → tm-if tm-false e₁ e₂ ↦ e₂
  s-if-step : ∀ e₁ e₁' e₂ e₃
    → e₁ ↦ e₁'
    → tm-if e₁ e₂ e₃ ↦ tm-if e₁' e₂ e₃
  s-app : ∀ e₁ e₂ x τ e
    {- → tm-app e₁ e₂ ↦ (e [ e₂ / x ]) -}
    → tm-app (tm-abs x τ e₁) e₂ ↦ e
  s-app-step : ∀ e₁ e₁' e₂
    → e₁ ↦ e₁'
    → tm-app e₁ e₂ ↦ tm-app e₁' e₂

data progress (e : Term) : Set where
  step : ∀ e'
    → e ↦ e'
    → progress e
  value :
    Value e
    → progress e

{- p-ty-weak : ∀ x e τ
  → ∅ ⊢ e ∶ τ
  → (x ↪ τ :: Γ) ⊢ e ∶ τ -}

p-ty-subst : ∀ x eₓ τₓ e τ e'
  → ∅ ⊢ eₓ ∶ τₓ 
  → (x ↪ τₓ :: ∅) ⊢ e ∶ τ
  → e [ eₓ / x ]⇛ e'
  → ∅ ⊢ e' ∶ τ
p-ty-subst x eₓ τₓ e τ e' _ (t-true (x ↪ τₓ :: ∅)) (subst-true x eₓ) = t-true ∅
p-ty-subst x eₓ τₓ e τ e' _ (t-false (x ↪ τₓ :: ∅)) (subst-false x eₓ) = t-false ∅
{- p-ty-subst x eₓ τₓ e τ e' teₓ (t-var (x ↪ τₓ :: ∅) y τ (∈-b x τₓ ∅)) (subst-var-ne x eₓ y) = _ {- t-var (x ↪ τₓ :: ∅) x τₓ (∈-b x τₓ ∅) -}
p-ty-subst x eₓ τₓ e τ e' teₓ (t-var (x ↪ τₓ :: ∅) x τ (∈-b x τₓ ∅)) (subst-var-eq x eₓ) = teₓ -}
p-ty-subst x eₓ τₓ e τ e' teₓ (t-if (x ↪ τₓ :: ∅) τ e₁ e₂ e₃ te₁ te₂ te₃) (subst-if x eₓ e₁ e₂ e₃ e₁' e₂' e₃' se₁' se₂' se₃') =
  let te₁' : ∅  ⊢ e₁' ∶ ty-bool
      te₁' = p-ty-subst x eₓ τₓ e₁ ty-bool e₁' teₓ te₁ se₁' in
  let te₂' : ∅  ⊢ e₂' ∶ τ
      te₂' = p-ty-subst x eₓ τₓ e₂ τ e₂' teₓ te₂ se₂' in
  let te₃' : ∅  ⊢ e₃' ∶ τ
      te₃' = p-ty-subst x eₓ τₓ e₃ τ e₃' teₓ te₃ se₃' in
  t-if ∅ τ e₁' e₂' e₃' te₁' te₂' te₃'
p-ty-subst x eₓ τₓ e τ e' teₓ (t-abs (x ↪ τₓ :: ∅) y τ₁ τ₂ e₂ te₂) (subst-abs x eₓ y τ₁ e₂ e₂' se') =
  t-abs ∅ y τ₁ τ₂ e₂' _
p-ty-subst x eₓ τₓ e τ e' teₓ (t-app (x ↪ τₓ :: ∅) e₁ e₂ τ₁ τ₂ te₁ te₂) (subst-app x eₓ e₁ e₂ e₁' e₂' se₁ se₂) =
  let te₁' : ∅ ⊢ e₁' ∶ ty-abs τ₁ τ₂
      te₁' = p-ty-subst x eₓ τₓ e₁ (ty-abs τ₁ τ₂) e₁' teₓ te₁ se₁ in
  let te₂' : ∅ ⊢ e₂' ∶ τ₂
      te₂' = p-ty-subst x eₓ τₓ e₂ τ₂ e₂' teₓ te₂ se₂ in
  t-app ∅ e₁' e₂' τ₁ τ₂ te₁' te₂'

{- p-ty-subst Γ x τₓ eₓ e τ  e' (t-abs (x ↪ τₓ :: Γ) y τ₁ τ₂ e'' te'') _ _ = _ -}

{-
p-progress : ∀ e τ → (∅ ⊢ e ∶ τ) → progress e
p-progress e τ (t-true ∅) = value v-true
p-progress e τ (t-false ∅) = value v-false
p-progress e τ (t-if ∅ τ e₁ e₂ e₃ te₁ _ _) with p-progress e₁ ty-bool te₁
... | value v-true = step e₂ (s-if-true e₂ e₃)
... | value v-false = step e₃ (s-if-false e₂ e₃)
... | step e₁' pe₁ = step (tm-if e₁' e₂ e₃) (s-if-step e₁ e₁' e₂ e₃ pe₁)
p-progress e τ (t-abs ∅ x τ₁ τ₂ e' _) = value (v-abs x τ₁ e')
p-progress e τ (t-var ∅ x τ ())
p-progress e τ (t-app ∅ e₁ e₂ τ₁ τ₂ te₁ _) with p-progress e₁ (ty-abs τ₁ τ₂) te₁
... | step e₁' pe₁ = step (tm-app e₁' e₂) (s-app-step e₁ e₁' e₂ pe₁) -}
{- ... | value (v-abs x τ₁ e') = step (tm) () -}
