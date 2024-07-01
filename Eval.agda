open import Syntax

-- The value relation, which describes which terms are values.
data Value : Term → Set where
  v-true  : Value tm-true
  v-false : Value tm-false
  v-abs   : ∀ x τ e → Value (tm-abs x τ e)

-- The stepping relation, which describes an evaluation step for a term.
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
