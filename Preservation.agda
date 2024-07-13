open import Ctx
open import Eval
open import Subst
open import Syntax
open import Typing

preserve : ∀ {e e' τ}
  → ∅ ⊢ e ∶ τ
  → e ↦ e'
  → ∅ ⊢ e' ∶ τ
preserve (ty-if _ te₂ _) (s-if-true e₂ e₃) =
  te₂
preserve (ty-if _ _ te₃) (s-if-false e₂ e₃) =
  te₃
preserve (ty-if te₁ te₂ te₃) (s-if-step e₁ e₁' e₂ e₃ se₁) =
  let te₁' : ∅ ⊢ e₁' ∶ t-bool
      te₁' = preserve te₁ se₁ in
  ty-if te₁' te₂ te₃
preserve (ty-app (ty-abs te₁) te₂) (s-app x τ₁ e₁ e₁' e₂ se₁) =
   subst-preserve-ty te₂ te₁ se₁
preserve (ty-app {τ₁ = τ₁} {τ₂} te₁ te₂) (s-app-step e₁ e₁' e₂ se₁) =
  let te₁' : ∅ ⊢ e₁' ∶ t-abs τ₁ τ₂
      te₁' = preserve te₁ se₁ in
  ty-app te₁' te₂
