open import Data.Product using (_×_) renaming (_,_ to ⟨_,_⟩)
open import Data.String.Properties using (_≟_)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≢_; sym; ≢-sym)
open import Relation.Nullary using (yes; no)

open import Ctx
open import Syntax
open import Typing

-- Context exchange, usually abbreviated as "ex", which is the permutation of
-- two assumptions of a context that does not invalidate any assumption of
-- this context.
data Exchange : Ctx → Ctx → Set where
  exchange : ∀ Γ Γ' x₁ τ₁ x₂ τ₂
    → x₁ ≢ x₂
    → Exchange (Γ , x₁ ∶ τ₁ , x₂ ∶ τ₂ , Γ') (Γ , x₂ ∶ τ₂ , x₁ ∶ τ₁ , Γ')

-- Monotonicity of exchange under extension, which means that if `Γ'` is an
-- exchange of `Γ`, then the extension of `Γ'` with the assumption `x ∶ τ`
-- is an exchange of the extension of `Γ` with `x ∶ τ`.
exchange-mono-ext : ∀ {Γ Γ'} x τ
  → Exchange Γ Γ'
  → Exchange (Γ , x ∶ τ) (Γ' , x ∶ τ)
exchange-mono-ext x τ (exchange Γ₁ Γ₂ x₁ τ₁ x₂ τ₂ x₁-≢-x₂) =
  exchange Γ₁ (Γ₂ , x ∶ τ) x₁ τ₁ x₂ τ₂ x₁-≢-x₂

-- Preservation of inclusion under exchange, which means that if the context `Γ'`
-- is an exchange of the context `Γ`, and the assumption `x ∶ τ` is in `Γ`,
-- then `x ∶ τ` is in `Γ'`.
exchange-preserve-in : ∀ {Γ Γ' x τ}
  → Exchange Γ Γ'
  → x ∶ τ ∈ Γ
  → x ∶ τ ∈ Γ'
exchange-preserve-in {x = x} {τ} (exchange Γ₁ Γ₂ x₁ τ₁ x₂ τ₂ x₁-≢-x₂) x-∈-Γ with in-concat-either-in-out (Γ₁ , x₁ ∶ τ₁ , x₂ ∶ τ₂) Γ₂ x τ x-∈-Γ
... | inj₁ ⟨ x-∈-Γ₁' , x-∉-Γ₂ ⟩ with x ≟ x₁
... | yes x-≡-x₁ rewrite x-≡-x₁ | in-unique x-∈-Γ₁' (∈-i (Γ₁ , x₁ ∶ τ₁) x₁ τ₁ x₂ τ₂ x₁-≢-x₂ (∈-b Γ₁ x₁ τ₁)) =
  let x-∈-Γ₁'' : x₁ ∶ τ₁ ∈ Γ₁ , x₂ ∶ τ₂ , x₁ ∶ τ₁
      x-∈-Γ₁'' = ∈-b (Γ₁ , x₂ ∶ τ₂) x₁ τ₁ in
  in-out-in-concat x-∈-Γ₁'' x-∉-Γ₂
... | no  x-≢-x₁ with x ≟ x₂
... | yes x-≡-x₂ rewrite x-≡-x₂ | in-unique x-∈-Γ₁' (∈-b (Γ₁ , x₁ ∶ τ₁) x₂ τ₂) =
  let x-∈-Γ₁'' : x₂ ∶ τ₂ ∈ Γ₁ , x₂ ∶ τ₂ , x₁ ∶ τ₁
      x-∈-Γ₁'' = ∈-i (Γ₁ , x₂ ∶ τ₂) x₂ τ₂ x₁ τ₁ (≢-sym x₁-≢-x₂) (∈-b Γ₁ x₂ τ₂)  in
  in-out-in-concat x-∈-Γ₁'' x-∉-Γ₂
... | no  x-≢-x₂ =
  let x-∈-Γ₁ : x ∶ τ ∈ Γ₁
      x-∈-Γ₁ = in-ext-distinct-in x-≢-x₁ (in-ext-distinct-in x-≢-x₂ x-∈-Γ₁') in
  let x-∈-Γ₁'' : x ∶ τ ∈ Γ₁ , x₂ ∶ τ₂ , x₁ ∶ τ₁
      x-∈-Γ₁'' = ∈-i (Γ₁ , x₂ ∶ τ₂) x τ x₁ τ₁ x-≢-x₁ (∈-i Γ₁ x τ x₂ τ₂ x-≢-x₂ x-∈-Γ₁) in
  in-out-in-concat x-∈-Γ₁'' x-∉-Γ₂
exchange-preserve-in {x = x} {τ} (exchange Γ₁ Γ₂ x₁ τ₁ x₂ τ₂ x₁-≢-x₂) x-∈-Γ | inj₂ x-∈-Γ₂ =
  in-in-concat (Γ₁ , x₂ ∶ τ₂ , x₁ ∶ τ₁) x-∈-Γ₂

-- Preservation of typing under exchange, which means that if the context `Γ'`
-- is an exchange of the context `Γ`, and that the term `e` has type `τ` under `Γ`,
-- then `e` also has type `τ` under `Γ'`.
exchange-preserve-ty : ∀ {Γ Γ' e τ}
  → Exchange Γ Γ'
  → Γ ⊢ e ∶ τ
  → Γ' ⊢ e ∶ τ
exchange-preserve-ty _ ty-true = ty-true
exchange-preserve-ty _ ty-false = ty-false
exchange-preserve-ty {Γ' = Γ'} ex (ty-var {x = x} {τ} x-∈-Γ) =
  let x-∈-Γ' : x ∶ τ ∈ Γ'
      x-∈-Γ' = exchange-preserve-in ex x-∈-Γ in
  ty-var x-∈-Γ'
exchange-preserve-ty {Γ' = Γ'} ex (ty-if {τ = τ} {e₁} {e₂} {e₃} te₁ te₂ te₃) =
  let te₁' : Γ' ⊢ e₁ ∶ t-bool
      te₁' = exchange-preserve-ty ex te₁ in
  let te₂' : Γ' ⊢ e₂ ∶ τ
      te₂' = exchange-preserve-ty ex te₂ in
  let te₃' : Γ' ⊢ e₃ ∶ τ
      te₃' = exchange-preserve-ty ex te₃ in
  ty-if te₁' te₂' te₃'
exchange-preserve-ty {Γ' = Γ'} ex (ty-abs {Γ} {x} {e₂} {τ₁} {τ₂} te₂) =
  let ex' : Exchange (Γ , x ∶ τ₁) (Γ' , x ∶ τ₁)
      ex' = exchange-mono-ext x τ₁ ex in
  let te₂' : (Γ' , x ∶ τ₁) ⊢ e₂ ∶ τ₂
      te₂' = exchange-preserve-ty ex' te₂ in
  ty-abs te₂'
exchange-preserve-ty {Γ' = Γ'} ex (ty-app {e₁ = e₁} {e₂} {τ₁} {τ} te₁ te₂) =
  let te₁' : Γ' ⊢ e₁ ∶ t-abs τ₁ τ
      te₁' = exchange-preserve-ty ex te₁ in
  let te₂' : Γ' ⊢ e₂ ∶ τ₁
      te₂' = exchange-preserve-ty ex te₂ in
  ty-app te₁' te₂'
