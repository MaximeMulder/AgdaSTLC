open import Ctx
open import Syntax

-- The typing relation, which describes a well-typed term and its type.
data _⊢_∶_ : Ctx → Term → Type → Set where
  ty-true : ∀ {Γ}
    → Γ ⊢ e-true ∶ t-bool
  ty-false : ∀ {Γ}
    → Γ ⊢ e-false ∶ t-bool
  ty-var : ∀ {Γ x τ}
    → x ∶ τ ∈ Γ
    → Γ ⊢ e-var x ∶ τ
  ty-if : ∀ {Γ τ e₁ e₂ e₃}
    → Γ ⊢ e₁ ∶ t-bool
    → Γ ⊢ e₂ ∶ τ
    → Γ ⊢ e₃ ∶ τ
    → Γ ⊢ e-if e₁ e₂ e₃ ∶ τ
  ty-abs : ∀ {Γ x e τ₁ τ₂}
    → (Γ , x ∶ τ₁) ⊢ e ∶ τ₂
    → Γ ⊢ e-abs x τ₁ e ∶ t-abs τ₁ τ₂
  ty-app : ∀ {Γ e₁ e₂ τ₁ τ₂}
    → Γ ⊢ e₁ ∶ t-abs τ₁ τ₂
    → Γ ⊢ e₂ ∶ τ₁
    → Γ ⊢ e-app e₁ e₂ ∶ τ₂
