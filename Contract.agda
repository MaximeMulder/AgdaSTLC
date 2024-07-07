open import Data.Product using (_×_) renaming (_,_ to ⟨_,_⟩)
open import Data.String.Properties using (_≟_)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≢_; sym; ≢-sym)
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Negation using (contradiction)

open import Ctx
open import Syntax
open import Typing

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

-- Preservation of typing under contraction, which means that if the context `Γ'` is
-- a contraction of the context `Γ`, and that the term `e` has type `τ` under `Γ`,
-- then `e` also has type `τ` under `Γ'`.
contract-preserve-ty : ∀ Γ Γ' e τ
  → Contract Γ Γ'
  → Γ ⊢ e ∶ τ
  → Γ' ⊢ e ∶ τ
contract-preserve-ty Γ Γ' _ _ _ (ty-true Γ) = ty-true Γ'
contract-preserve-ty Γ Γ' _ _ _  (ty-false Γ) = ty-false Γ'
contract-preserve-ty Γ Γ' _ _ c (ty-var Γ x τ x-∈-Γ) =
  let x-∈-Γ' : x ∶ τ ∈ Γ'
      x-∈-Γ' = contract-preserve-in Γ Γ' x τ c x-∈-Γ in
  ty-var Γ' x τ x-∈-Γ'
contract-preserve-ty Γ Γ' _ τ c (ty-if Γ τ e₁ e₂ e₃ te₁ te₂ te₃) =
  let te₁' : Γ' ⊢ e₁ ∶ t-bool
      te₁' = contract-preserve-ty Γ Γ' e₁ t-bool c te₁ in
  let te₂' : Γ' ⊢ e₂ ∶ τ
      te₂' = contract-preserve-ty Γ Γ' e₂ τ c te₂ in
  let te₃' : Γ' ⊢ e₃ ∶ τ
      te₃' = contract-preserve-ty Γ Γ' e₃ τ c te₃ in
  ty-if Γ' τ e₁ e₂ e₃ te₁' te₂' te₃'
contract-preserve-ty Γ Γ' _ _ c (ty-abs Γ x e₂ τ₁ τ₂ te₂) =
  let c' : Contract (Γ , x ∶ τ₁) (Γ' , x ∶ τ₁)
      c' = contract-mono-ext Γ Γ' x τ₁ c in
  let te₂' : (Γ' , x ∶ τ₁) ⊢ e₂ ∶ τ₂
      te₂' = contract-preserve-ty (Γ , x ∶ τ₁) (Γ' , x ∶ τ₁) e₂ τ₂ c' te₂ in
  ty-abs Γ' x e₂ τ₁ τ₂ te₂'
contract-preserve-ty Γ Γ' _ τ c (ty-app Γ e₁ e₂ τ₁ τ te₁ te₂) =
  let te₁' : Γ' ⊢ e₁ ∶ t-abs τ₁ τ
      te₁' = contract-preserve-ty Γ Γ' e₁ (t-abs τ₁ τ) c te₁ in
  let te₂' : Γ' ⊢ e₂ ∶ τ₁
      te₂' = contract-preserve-ty Γ Γ' e₂ τ₁ c te₂ in
  ty-app Γ' e₁ e₂ τ₁ τ te₁' te₂'
