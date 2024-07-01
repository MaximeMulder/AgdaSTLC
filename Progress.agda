-- TODO: This file is old code, it likely needs a full rewrite

-- Proof of progress !

open import Eval
open import Syntax

data Progress (e : Term) : Set where
  progress-s : ∀ e'
    → e ↦ e'
    → Progress e
  progress-v :
    Value e
    → Progress e

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
