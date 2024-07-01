open import Data.String.Properties using (_≟_)
open import Relation.Nullary using (yes; no)

open import Ctx

-- Context contraction, which is the deletion of an entry in a context that
-- does not invalidate any information in this context.
data Contract : Ctx → Ctx → Set where
  contract : ∀ Γ₁ Γ₂ x τ τ₂
    → x ∶ τ₂ ∈ Γ₂
    → Contract (Γ₁ , x ∶ τ , Γ₂) (Γ₁ , Γ₂)

{- -- Preservation of inclusion under contraction, which means that if the context `Γ'`
-- is a contraction of the context `Γ`, and the entry `x ∶ τ` is in `Γ`, then `x ∶ τ`
-- is in `Γ'`.
in-contract : ∀ Γ Γ' x τ
  → Contract Γ Γ'
  → x ∶ τ ∈ Γ
  → x ∶ τ ∈ Γ'
in-contract Γ Γ' x τ (contract Γ₁ Γ₂ x' τ' τ₂ x'-∈-Γ₂) x-∈-Γ with x ≟ x'
... | yes x-≡-x' rewrite x-≡-x' = _
... | no  x-≢-x' = _ -}

-- TODO: Prove
postulate
  contract-preserve-in : ∀ Γ Γ' x τ
    → Contract Γ Γ'
    → x ∶ τ ∈ Γ
    → x ∶ τ ∈ Γ'
