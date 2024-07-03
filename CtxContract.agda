open import Data.Product using (_×_) renaming (_,_ to ⟨_,_⟩)
open import Data.String.Properties using (_≟_)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≢_; sym; ≢-sym)
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Negation using (contradiction)

open import Ctx

-- Context contraction, usually abbreviated as "contract", which is the deletion
-- of an assumption of a context that does not invalidate any assumption of this
-- context.
data Contract : Ctx → Ctx → Set where
  contract : ∀ Γ₁ Γ₂ x τ τ₂
    → x ∶ τ₂ ∈ Γ₂
    → Contract (Γ₁ , x ∶ τ , Γ₂) (Γ₁ , Γ₂)

-- Monotonicity of contraction under extension, which means that if `Γ'` is a
-- contraction of `Γ`, then the extension of `Γ'` with the assumption `x ∶ τ`
-- is a contraction of the extension of `Γ` with `x ∶ τ`.
contract-mono-ext : ∀ Γ Γ' x τ
  → Contract Γ Γ'
  → Contract (Γ , x ∶ τ) (Γ' , x ∶ τ)
contract-mono-ext _ _ x τ (contract Γ₁ Γ₂ x' τ' τ₂ x'-∈-Γ₂) with x ≟ x'
... | yes x-≡-x' rewrite sym x-≡-x' =
  contract Γ₁ (Γ₂ , x ∶ τ) x τ' τ (∈-b Γ₂ x τ)
... | no  x-≢-x' =
  let x'-∈-Γ₂' : x' ∶ τ₂ ∈ Γ₂ , x ∶ τ
      x'-∈-Γ₂' = ∈-i Γ₂ x' τ₂ x τ (≢-sym x-≢-x') x'-∈-Γ₂ in
  contract Γ₁ (Γ₂ , x ∶ τ) x' τ' τ₂ x'-∈-Γ₂'

-- Preservation of inclusion under contraction, which means that if the context `Γ'`
-- is a contraction of the context `Γ`, and the assumption `x ∶ τ` is in `Γ`,
-- then `x ∶ τ` is in `Γ'`.
contract-preserve-in : ∀ Γ Γ' x τ
  → Contract Γ Γ'
  → x ∶ τ ∈ Γ
  → x ∶ τ ∈ Γ'
contract-preserve-in Γ Γ' x τ (contract Γ₁ Γ₂ x' τ' τ₂ x'-∈-Γ₂) x-∈-Γ with in-concat-either-in-out (Γ₁ , x' ∶ τ') Γ₂ x τ x-∈-Γ
... | inj₁ ⟨ x-∈-Γ₁' , x-∉-Γ₂ ⟩ with x ≟ x'
... | yes x-≡-x' =
  let x-≢-x' : x ≢ x'
      x-≢-x' = ≢-sym (in-out-distinct Γ₂ x' x τ₂ x'-∈-Γ₂ x-∉-Γ₂) in
  contradiction x-≡-x' x-≢-x'
... | no  x-≢-x' =
  let x-∈-Γ₁ : x ∶ τ ∈ Γ₁
      x-∈-Γ₁ = in-ext-distinct-in Γ₁ x τ x' τ' x-≢-x' x-∈-Γ₁' in
  in-out-in-concat Γ₁ Γ₂ x τ x-∈-Γ₁ x-∉-Γ₂
contract-preserve-in Γ  Γ' x τ (contract Γ₁ Γ₂ x' τ' τ₂ x'-∈-Γ₂) x-∈-Γ | inj₂ x-∈-Γ₂ =
  in-in-concat Γ₁ Γ₂ x τ x-∈-Γ₂
