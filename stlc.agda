open import Agda.Builtin.String
open import Relation.Binary.PropositionalEquality using (_≡_)

data Type : Set where
  ty-bool : Type
  ty-abs  : Type → Type → Type

data Ctx : Set  where
  ∅ : Ctx
  _↪_::_ : String → Type → Ctx →  Ctx

data Term : Set where
  tm-true  : Term
  tm-false : Term
  tm-var   : String →  Term
  tm-abs   : String → Type → Term → Term
  tm-app   : Term → Term → Term
  tm-if    : Term → Term → Term → Term

{- _[_/_] : Term → Term → String → Term
_[_/_] (tm-var x₁) e x₂ = e
_[_/_] e _ _ = e -}

{- data _[_/_] (x : String ) : Term → Term → Set where
  subst-var : (tm-var x')
    → x ≡ x'
    → -}

data _↪_∈_ : String → Type → Ctx → Set where
  B : ∀ x τ Γ
    → x ↪ τ ∈ (x ↪ τ :: Γ)
  I : ∀ x₁ x₂ τ₁ τ₂ Γ
    → x₁ ↪ τ₁ ∈ Γ
    → x₁ ↪ τ₁ ∈ (x₂ ↪ τ₂ :: Γ)

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
  t-app : ∀ Γ τ₁ τ₂ e₁ e₂
    → Γ ⊢ e₁ ∶ ty-abs τ₁ τ₂
    → Γ ⊢ e₂ ∶ τ₂
    → Γ ⊢ tm-app e₁ e₂ ∶ τ₂

data Value : Term → Set where
  v-true  : Value tm-true
  v-false : Value tm-false
  v-abs   : ∀ x τ e → Value (tm-abs x τ e)

data _↦_ : Term → Term → Set where
  s-if-step : ∀ e₁ e₁' e₂ e₃
    → e₁ ↦ e₁'
    → tm-if e₁ e₂ e₃ ↦ tm-if e₁' e₂ e₃
  s-if-true : ∀ e₁ e₂
    → tm-if tm-true e₁ e₂ ↦ e₁
  s-if-false : ∀ e₁ e₂
    → tm-if tm-false e₁ e₂ ↦ e₂
  s-app-step : ∀ e₁ e₁' e₂
    → e₁ ↦ e₁'
    → tm-app e₁ e₂ ↦ tm-app e₁' e₂
  s-app : ∀ e₁ e₂ x τ e
    {- → tm-app e₁ e₂ ↦ (e [ e₂ / x ]) -}
    → tm-app (tm-abs x τ e₁) e₂ ↦ e

data progress (e : Term) : Set where
  step : ∀ e'
    → e ↦ e'
    → progress e
  value :
    Value e
    → progress e

{- ∀ Γ x τ e τ' → (x ↪ τ :: Γ) ⊢ e ∶ τ' → Γ ⊢ e[τ/x] ∶ τ' -}

proof-progress : ∀ e τ → (∅ ⊢ e ∶ τ) → progress e
proof-progress e τ (t-true ∅) = value v-true
proof-progress e τ (t-false ∅) = value v-false
proof-progress e τ (t-if ∅ τ e₁ e₂ e₃ te₁ _ _) with proof-progress e₁ ty-bool te₁
... | value v-true = step e₂ (s-if-true e₂ e₃)
... | value v-false = step e₃ (s-if-false e₂ e₃)
... | step e₁' pe₁ = step (tm-if e₁' e₂ e₃) (s-if-step e₁ e₁' e₂ e₃ pe₁)
proof-progress e τ (t-abs ∅ x τ₁ τ₂ e' _) = value (v-abs x τ₁ e')
proof-progress e τ (t-var ∅ x τ ())
proof-progress e τ (t-app ∅ τ₁ τ₂ e₁ e₂ te₁ _) with proof-progress e₁ (ty-abs τ₁ τ₂) te₁
... | step e₁' pe₁ = step (tm-app e₁' e₂) (s-app-step e₁ e₁' e₂ pe₁)
{- ... | value (v-abs x τ₁ e') = step (tm) () -}
