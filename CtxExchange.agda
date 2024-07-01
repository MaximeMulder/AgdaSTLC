-- TODO: This file is old code, it likely needs a full rewrite (if I actually need it).

data Exchange : Ctx → Ctx → Set where
  exchange : ∀ Γ Γ' x₁ τ₁ x₂ τ₂
    → x₁ ≢ x₂
    → Exchange (Γ , x₁ ∶ τ₁ , x₂ ∶ τ₂ , Γ') (Γ , x₂ ∶ τ₂ , x₁ ∶ τ₁ , Γ')

{-
  Inclusion is preserved under exchange.
-}
{- p-in-exchange : ∀ Γ Γ' x τ
  → Exchange Γ Γ'
  → x ∶ τ ∈ Γ
  → x ∶ τ ∈ Γ'
p-in-exchange Γ Γ' x τ (exchange aa bb x₁ τ₁ x₂ τ₂ ≢-x₁₂) (∈-i _ x τ x₂ τ₂ ≢-x₂ (∈-i _ x τ x₁ τ₁ ≢-x₁ ∈-x-Γₚ)) =
  ∈-i _ x τ x₁ τ₁ ≢-x₁ (∈-i _ _ _ _ _ ≢-x₂ ∈-x-Γₚ)
p-in-exchange Γ Γ' x τ (exchange aa bb x₁ τ₁ x₂ τ₂ ≢-x₁₂) (∈-i _ x τ x₂ τ₂ ≢-x₂ (∈-b _ x τ)) =
  ∈-b _ x τ
p-in-exchange Γ Γ' x τ (exchange aa bb x₁ τ₁ x₂ τ₂ ≢-x₁₂) (∈-b _ x₂ τ₂) with x ≟ x₁
... | no  ≢-x₁ = ∈-i _ x τ x₁ τ₁ ≢-x₁ (∈-b _ x τ)
... | yes ≡-x₁ = ∈-i _ x₂ τ₂ x₁ τ₁ (≢-sym ≢-x₁₂) (∈-b _ x₂ τ₂) -}

-- TODO: This would probably need to be in the typing file.
{-
  Typing is preserved under exchange.
-}
{- p-ty-exchange : ∀ Γ Γ' e τ
  → Exchange Γ Γ'
  → Γ ⊢ e ∶ τ
  → Γ' ⊢ e ∶ τ
p-ty-exchange Γ Γ' tm-true ty-bool _ (t-true Γ) = t-true Γ'
p-ty-exchange Γ Γ' tm-false ty-bool _ (t-false Γ) = t-false Γ'
p-ty-exchange Γ Γ' (tm-if e₁ e₂ e₃) τ p (t-if Γ τ e₁ e₂ e₃ te₁ te₂ te₃) =
  let te₁' : Γ' ⊢ e₁ ∶ ty-bool
      te₁' = p-ty-exchange Γ Γ' e₁ ty-bool p te₁ in
  let te₂' : Γ' ⊢ e₂ ∶ τ
      te₂' = p-ty-exchange Γ Γ' e₂ τ p te₂ in
  let te₃' : Γ' ⊢ e₃ ∶ τ
      te₃' = p-ty-exchange Γ Γ' e₃ τ p te₃ in
  t-if Γ' τ e₁ e₂ e₃ te₁' te₂' te₃'
p-ty-exchange Γ Γ' (tm-var x) τ p (t-var Γ x τ ∈-x-τ-Γ) =
  t-var Γ' x τ (p-in-exchange Γ Γ' x τ p ∈-x-τ-Γ)
p-ty-exchange Γ Γ' (tm-app e₁ e₂) τ₂ p (t-app Γ e₁ e₂ τ₁ τ₂ te₁ te₂) =
  let te₁' : Γ' ⊢ e₁ ∶ ty-abs τ₁ τ₂
      te₁' = p-ty-exchange Γ Γ' e₁ (ty-abs τ₁ τ₂) p te₁ in
  let te₂' : Γ' ⊢ e₂ ∶ τ₂
      te₂' = p-ty-exchange Γ Γ' e₂ τ₂ p te₂ in
  t-app Γ' e₁ e₂ τ₁ τ₂ te₁' te₂'
p-ty-exchange Γ Γ' (tm-abs x τ₁ e) _ p (t-abs Γ x τ₁ τ₂ e te₂) =
  t-abs Γ' x τ₁ τ₂ e _ -}
