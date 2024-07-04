open import Ctx
open import Eval
open import Subst
open import Syntax
open import Typing

data Progress (e : Term) : Set where
  progress-s : ∀ e'
    → e ↦ e'
    → Progress e
  progress-v :
    Value e
    → Progress e

progress : ∀ {e τ}
  → (∅ ⊢ e ∶ τ)
  → Progress e
progress (t-true ∅) =
  progress-v v-true
progress (t-false ∅) =
  progress-v v-false
progress (t-if ∅ τ e₁ e₂ e₃ te₁ _ _) with progress te₁
... | progress-v v-true =
  progress-s e₂ (s-if-true e₂ e₃)
... | progress-v v-false =
  progress-s e₃ (s-if-false e₂ e₃)
... | progress-s e₁' pe₁ =
  progress-s (tm-if e₁' e₂ e₃) (s-if-step e₁ e₁' e₂ e₃ pe₁)
progress (t-abs ∅ x e' τ₁ τ₂ _) =
  progress-v (v-abs x τ₁ e')
progress (t-var ∅ x τ ())
progress (t-app ∅ e₁ e₂ τ₁ τ₂ te₁ _) with progress te₁
... | progress-s e₁' pe₁ =
  progress-s (tm-app e₁' e₂) (s-app-step e₁ e₁' e₂ pe₁)
... | progress-v (v-abs x τ₁' e₁') with subst-total e₁' x e₂
... | ⟨ e₁'' , se₁'' ⟩ =
  progress-s e₁'' (s-app x τ₁' e₁' e₁'' e₂ se₁'')
