open import Subst
open import Syntax

-- The value relation, which describes which terms are values.
data Value : Term → Set where
  v-true  : Value e-true
  v-false : Value e-false
  v-abs   : ∀ x τ e → Value (e-abs x τ e)

-- The stepping relation, which describes an evaluation step for a term.
data _↦_ : Term → Term → Set where
  s-if-true : ∀ e₁ e₂
    → e-if e-true e₁ e₂ ↦ e₁
  s-if-false : ∀ e₁ e₂
    → e-if e-false e₁ e₂ ↦ e₂
  s-if-step : ∀ e₁ e₁' e₂ e₃
    → e₁ ↦ e₁'
    → e-if e₁ e₂ e₃ ↦ e-if e₁' e₂ e₃
  s-app : ∀ x τ e₁ e₁' e₂
    → e₁ [ e₂ / x ]⇛ e₁'
    → e-app (e-abs x τ e₁) e₂ ↦ e₁'
  s-app-step : ∀ e₁ e₁' e₂
    → e₁ ↦ e₁'
    → e-app e₁ e₂ ↦ e-app e₁' e₂
