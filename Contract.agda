open import Data.Product using (_×_) renaming (_,_ to ⟨_,_⟩)
open import Data.String.Properties using (_≟_)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≢_; sym; ≢-sym)
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Negation using (contradiction)

open import Ctx
open import Syntax
open import Typing

-- Context contraction, usually abbreviated as "contract" or "ct", which is the
-- deletion of an assumption of a context that does not invalidate any
-- assumption of this context.
data Contract : Ctx → Ctx → Set where
  contract : ∀ Γ₁ Γ₂ x τ τ₂
    → x ∶ τ₂ ∈ Γ₂
    → Contract (Γ₁ , x ∶ τ , Γ₂) (Γ₁ , Γ₂)

-- Monotonicity of contraction under extension, which means that if `Γ'` is a
-- contraction of `Γ`, then the extension of `Γ'` with the assumption `x ∶ τ`
-- is a contraction of the extension of `Γ` with `x ∶ τ`.
contract-mono-ext : ∀ {Γ Γ'} x τ
  → Contract Γ Γ'
  → Contract (Γ , x ∶ τ) (Γ' , x ∶ τ)
contract-mono-ext x τ (contract Γ₁ Γ₂ x' τ' τ₂ x'-∈-Γ₂) with x ≟ x'
... | yes x-≡-x' rewrite sym x-≡-x' =
  contract Γ₁ (Γ₂ , x ∶ τ) x τ' τ (∈-b Γ₂ x τ)
... | no  x-≢-x' =
  let x'-∈-Γ₂' : x' ∶ τ₂ ∈ Γ₂ , x ∶ τ
      x'-∈-Γ₂' = ∈-i Γ₂ x' τ₂ x τ (≢-sym x-≢-x') x'-∈-Γ₂ in
  contract Γ₁ (Γ₂ , x ∶ τ) x' τ' τ₂ x'-∈-Γ₂'

-- Preservation of inclusion under contraction, which means that if the context `Γ'`
-- is a contraction of the context `Γ`, and the assumption `x ∶ τ` is in `Γ`,
-- then `x ∶ τ` is in `Γ'`.
contract-preserve-in : ∀ {Γ Γ' x τ}
  → Contract Γ Γ'
  → x ∶ τ ∈ Γ
  → x ∶ τ ∈ Γ'
contract-preserve-in {x = x} {τ} (contract Γ₁ Γ₂ x' τ' τ₂ x'-∈-Γ₂) x-∈-Γ with in-concat-either-in-out (Γ₁ , x' ∶ τ') Γ₂ x τ x-∈-Γ
... | inj₁ ⟨ x-∈-Γ₁' , x-∉-Γ₂ ⟩ with x ≟ x'
... | yes x-≡-x' =
  let x-≢-x' : x ≢ x'
      x-≢-x' = ≢-sym (in-out-distinct x'-∈-Γ₂ x-∉-Γ₂) in
  contradiction x-≡-x' x-≢-x'
... | no  x-≢-x' =
  let x-∈-Γ₁ : x ∶ τ ∈ Γ₁
      x-∈-Γ₁ = in-ext-distinct-in x-≢-x' x-∈-Γ₁' in
  in-out-in-concat x-∈-Γ₁ x-∉-Γ₂
contract-preserve-in {x = x} {τ} (contract Γ₁ Γ₂ x' τ' τ₂ x'-∈-Γ₂) x-∈-Γ | inj₂ x-∈-Γ₂ =
  in-in-concat Γ₁ x-∈-Γ₂

-- Preservation of typing under contraction, which means that if the context `Γ'` is
-- a contraction of the context `Γ`, and that the term `e` has type `τ` under `Γ`,
-- then `e` also has type `τ` under `Γ'`.
contract-preserve-ty : ∀ {Γ Γ' e τ}
  → Contract Γ Γ'
  → Γ ⊢ e ∶ τ
  → Γ' ⊢ e ∶ τ
contract-preserve-ty _ ty-true =
  ty-true
contract-preserve-ty _ ty-false =
  ty-false
contract-preserve-ty {Γ' = Γ'} ct (ty-var {x = x} {τ} x-∈-Γ) =
  let x-∈-Γ' : x ∶ τ ∈ Γ'
      x-∈-Γ' = contract-preserve-in ct x-∈-Γ in
  ty-var x-∈-Γ'
contract-preserve-ty {Γ' = Γ'} ct (ty-if {τ = τ} {e₁} {e₂} {e₃} te₁ te₂ te₃) =
  let te₁' : Γ' ⊢ e₁ ∶ t-bool
      te₁' = contract-preserve-ty ct te₁ in
  let te₂' : Γ' ⊢ e₂ ∶ τ
      te₂' = contract-preserve-ty ct te₂ in
  let te₃' : Γ' ⊢ e₃ ∶ τ
      te₃' = contract-preserve-ty ct te₃ in
  ty-if te₁' te₂' te₃'
contract-preserve-ty {Γ' = Γ'} ct (ty-abs {Γ} {x} {e₂} {τ₁} {τ₂} te₂) =
  let ct' : Contract (Γ , x ∶ τ₁) (Γ' , x ∶ τ₁)
      ct' = contract-mono-ext x τ₁ ct in
  let te₂' : (Γ' , x ∶ τ₁) ⊢ e₂ ∶ τ₂
      te₂' = contract-preserve-ty ct' te₂ in
  ty-abs te₂'
contract-preserve-ty {Γ' = Γ'} ct (ty-app {e₁ = e₁} {e₂} {τ₁} {τ} te₁ te₂) =
  let te₁' : Γ' ⊢ e₁ ∶ t-abs τ₁ τ
      te₁' = contract-preserve-ty ct te₁ in
  let te₂' : Γ' ⊢ e₂ ∶ τ₁
      te₂' = contract-preserve-ty ct te₂ in
  ty-app te₁' te₂'
