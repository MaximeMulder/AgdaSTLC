open import Data.Product using (_×_) renaming (_,_ to ⟨_,_⟩)
open import Data.String.Properties using (_≟_)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≢_; sym; ≢-sym)
open import Relation.Nullary using (yes; no)

open import Ctx

-- Context exchange, which is the permutation of two assumptions of a context that
-- does not invalidate any assumption of this context.
data Exchange : Ctx → Ctx → Set where
  exchange : ∀ Γ Γ' x₁ τ₁ x₂ τ₂
    → x₁ ≢ x₂
    → Exchange (Γ , x₁ ∶ τ₁ , x₂ ∶ τ₂ , Γ') (Γ , x₂ ∶ τ₂ , x₁ ∶ τ₁ , Γ')

-- Preservation of inclusion under exchange, which means that if the context `Γ'`
-- is a exchange of the context `Γ`, and the assumption `x ∶ τ` is in `Γ`,
-- then `x ∶ τ` is in `Γ'`.
exchange-preserve-in : ∀ Γ Γ' x τ
  → Exchange Γ Γ'
  → x ∶ τ ∈ Γ
  → x ∶ τ ∈ Γ'
exchange-preserve-in Γ Γ' x τ (exchange Γ₁ Γ₂ x₁ τ₁ x₂ τ₂ x₁-≢-x₂) x-∈-Γ with in-concat-either-in-out (Γ₁ , x₁ ∶ τ₁ , x₂ ∶ τ₂) Γ₂ x τ x-∈-Γ
... | inj₁ ⟨ x-∈-Γ₁' , x-∉-Γ₂ ⟩ with x ≟ x₁
... | yes x-≡-x₁ rewrite x-≡-x₁ | in-unique (Γ₁ , x₁ ∶ τ₁ , x₂ ∶ τ₂) x₁ τ τ₁ x-∈-Γ₁' (∈-i (Γ₁ , x₁ ∶ τ₁) x₁ τ₁ x₂ τ₂ x₁-≢-x₂ (∈-b Γ₁ x₁ τ₁)) =
  let x-∈-Γ₁'' : x₁ ∶ τ₁ ∈ Γ₁ , x₂ ∶ τ₂ , x₁ ∶ τ₁
      x-∈-Γ₁'' = ∈-b (Γ₁ , x₂ ∶ τ₂) x₁ τ₁ in
  in-out-in-concat (Γ₁ , x₂ ∶ τ₂ , x₁ ∶ τ₁) Γ₂ x₁ τ₁ x-∈-Γ₁'' x-∉-Γ₂
... | no  x-≢-x₁ with x ≟ x₂
... | yes x-≡-x₂ rewrite x-≡-x₂ | in-unique (Γ₁ , x₁ ∶ τ₁ , x₂ ∶ τ₂) x₂ τ τ₂ x-∈-Γ₁' (∈-b (Γ₁ , x₁ ∶ τ₁) x₂ τ₂) =
  let x-∈-Γ₁'' : x₂ ∶ τ₂ ∈ Γ₁ , x₂ ∶ τ₂ , x₁ ∶ τ₁
      x-∈-Γ₁'' = ∈-i (Γ₁ , x₂ ∶ τ₂) x₂ τ₂ x₁ τ₁ (≢-sym x₁-≢-x₂) (∈-b Γ₁ x₂ τ₂)  in
  in-out-in-concat (Γ₁ , x₂ ∶ τ₂ , x₁ ∶ τ₁) Γ₂ x₂ τ₂ x-∈-Γ₁'' x-∉-Γ₂
... | no  x-≢-x₂ =
  let x-∈-Γ₁ : x ∶ τ ∈ Γ₁
      x-∈-Γ₁ = in-ext-distinct-in Γ₁ x τ x₁ τ₁ x-≢-x₁ (in-ext-distinct-in (Γ₁ , x₁ ∶ τ₁) x τ x₂ τ₂ x-≢-x₂ x-∈-Γ₁') in
  let x-∈-Γ₁'' : x ∶ τ ∈ Γ₁ , x₂ ∶ τ₂ , x₁ ∶ τ₁
      x-∈-Γ₁'' = ∈-i (Γ₁ , x₂ ∶ τ₂) x τ x₁ τ₁ x-≢-x₁ (∈-i Γ₁ x τ x₂ τ₂ x-≢-x₂ x-∈-Γ₁) in
  in-out-in-concat (Γ₁ , x₂ ∶ τ₂ , x₁ ∶ τ₁) Γ₂ x τ x-∈-Γ₁'' x-∉-Γ₂
exchange-preserve-in Γ Γ' x τ (exchange Γ₁ Γ₂ x₁ τ₁ x₂ τ₂ x₁-≢-x₂) x-∈-Γ | inj₂ x-∈-Γ₂ =
  in-in-concat (Γ₁ , x₂ ∶ τ₂ , x₁ ∶ τ₁) Γ₂ x τ x-∈-Γ₂

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
