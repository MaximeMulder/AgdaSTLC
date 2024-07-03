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

-- Monotonicity of exchange under extension, which means that if `Γ'` is an
-- exchange of `Γ`, then the extension of `Γ'` with the assumption `x ∶ τ`
-- is an exchange of the extension of `Γ` with `x ∶ τ`.
exchange-mono-ext : ∀ Γ Γ' x τ
  → Exchange Γ Γ'
  → Exchange (Γ , x ∶ τ) (Γ' , x ∶ τ)
exchange-mono-ext Γ Γ' x τ (exchange Γ₁ Γ₂ x₁ τ₁ x₂ τ₂ x₁-≢-x₂) =
  exchange Γ₁ (Γ₂ , x ∶ τ) x₁ τ₁ x₂ τ₂ x₁-≢-x₂

-- Preservation of inclusion under exchange, which means that if the context `Γ'`
-- is an exchange of the context `Γ`, and the assumption `x ∶ τ` is in `Γ`,
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
