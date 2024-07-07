open import Ctx
open import Eval
open import Subst
open import Syntax
open import Typing

preserve : ∀ {e e' τ}
  → ∅ ⊢ e ∶ τ
  → e ↦ e'
  → ∅ ⊢ e' ∶ τ
preserve (t-if ∅ τ tm-true e₂ e₃ _ te₂ _) (s-if-true e₂ e₃) =
  te₂
preserve (t-if ∅ τ tm-false e₂ e₃ _ _ te₃) (s-if-false e₂ e₃) =
  te₃
preserve (t-if ∅ τ e₁ e₂ e₃ te₁ te₂ te₃) (s-if-step e₁ e₁' e₂ e₃ se₁) =
  let te₁' : ∅ ⊢ e₁' ∶ ty-bool
      te₁' = preserve te₁ se₁ in
  t-if ∅ τ e₁' e₂ e₃ te₁' te₂ te₃
preserve (t-app ∅ (tm-abs x τ₁ e₁) e₂ τ₁ τ₂ (t-abs ∅ x e₁ τ₁ τ₂ te₁) te₂) (s-app x τ₁ e₁ e₁' e₂ se₁) =
   subst-preserve-ty ∅ x e₂ τ₁ e₁ τ₂ e₁' te₂ te₁ se₁
preserve (t-app ∅ e₁ e₂ τ₁ τ₂ te₁ te₂) (s-app-step e₁ e₁' e₂ se₁) =
  let te₁' : ∅ ⊢ e₁' ∶ ty-abs τ₁ τ₂
      te₁' = preserve te₁ se₁ in
  t-app ∅ e₁' e₂ τ₁ τ₂ te₁' te₂
