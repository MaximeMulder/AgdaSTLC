open import Data.Nat using (suc)
open import Data.Product using (_×_) renaming (_,_ to ⟨_,_⟩)
open import Data.String.Properties using (_≟_)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; sym; ≢-sym)
open import Relation.Nullary using (yes; no)

open import Ctx
open import Syntax
open import Typing

-- Context weakening, usually abbreviated as "weaken" or "wk", which is the
-- insertion of an assumption in a context that does not invalidate any
-- assumption of this context.
data Weaken : Ctx → Ctx → Set where
  weaken-∉ : ∀ Γ₁ Γ₂ x τ
    → x ∉ Γ₁
    → Weaken (Γ₁ , Γ₂) (Γ₁ , x ∶ τ , Γ₂)
  weaken-∈ : ∀ Γ₁ Γ₂ x τ τ₂
    → x ∶ τ₂ ∈ Γ₂
    → Weaken (Γ₁ , Γ₂) (Γ₁ , x ∶ τ , Γ₂)

-- Reflexive transitive closure of the context extension.
data Weaken*  : Ctx → Ctx → Set where
  weaken*-base : ∀ {Γ Γ'}
    → Weaken Γ Γ'
    → Weaken* Γ Γ'
  weaken*-refl : ∀ Γ
    → Weaken* Γ Γ
  weaken*-trans : ∀ {Γ Γ' Γ''}
    → Weaken* Γ Γ'
    → Weaken* Γ' Γ''
    → Weaken* Γ Γ''

-- Monotonicity of weakening under extension, which means that if `Γ'` is a
-- weakening of `Γ`, then the extension of `Γ'` with the assumption `x ∶ τ` is a
-- weakening of the extension of `Γ` with `x ∶ τ`.
weaken-mono-ext : ∀ {Γ Γ'} x τ
  → Weaken Γ Γ'
  → Weaken (Γ , x ∶ τ) (Γ' , x ∶ τ)
weaken-mono-ext x τ (weaken-∉ Γ₁ Γ₂ x' τ' x'-∉-Γ₁) =
  weaken-∉ Γ₁ (Γ₂ , x ∶ τ) x' τ' x'-∉-Γ₁
weaken-mono-ext x τ (weaken-∈ Γ₁ Γ₂ x' τ' τ₂ x'-∈-Γ₂) with x ≟ x'
... | yes x-≡-x' rewrite sym x-≡-x' = weaken-∈ Γ₁ (Γ₂ , x ∶ τ) x τ' τ (∈-b Γ₂ x τ)
... | no  x-≢-x' = weaken-∈ Γ₁ (Γ₂ , x ∶ τ) x' τ' τ₂ (∈-i Γ₂ x' τ₂ x τ (≢-sym x-≢-x') x'-∈-Γ₂)

weaken*-nil-length : ∀ {Γ n} → Length Γ n → Weaken* ∅ Γ
weaken*-nil-length length-zero =
  weaken*-refl ∅
weaken*-nil-length (length-suc Γ n x τ length-Γ) with either-ex-in-out Γ x
... | inj₂ x-∉-Γ =
  let weak-∅-Γ : Weaken* ∅ Γ
      weak-∅-Γ = weaken*-nil-length length-Γ in
  let weak-Γ-x : Weaken Γ (Γ , x ∶ τ)
      weak-Γ-x = weaken-∉ Γ ∅ x τ x-∉-Γ in
  weaken*-trans weak-∅-Γ (weaken*-base weak-Γ-x)
... | inj₁ ⟨ _ , x-∈-Γ ⟩ with in-ex-concat x-∈-Γ
... | ⟨ Γ₁ , ⟨ Γ₂ , ⟨ τ' , ⟨ Γ₁₂-≡-Γ , x-∉-Γ₁ ⟩ ⟩ ⟩ ⟩ rewrite Γ₁₂-≡-Γ =
  let length-Γ' : Length (Γ₁ , (Γ₂ , x ∶ τ)) n
      length-Γ' = length-del Γ₁ (Γ₂ , x ∶ τ) x τ' n (length-suc (Γ₁ , x ∶ τ' , Γ₂) n x τ length-Γ) in
  let weak-∅-Γ : Weaken* ∅ (Γ₁ , (Γ₂ , x ∶ τ))
      weak-∅-Γ = weaken*-nil-length length-Γ' in
  let weak-Γ-x : Weaken* (Γ₁ , (Γ₂ , x ∶ τ)) ((Γ₁ , x ∶ τ') , (Γ₂ , x ∶ τ))
      weak-Γ-x = weaken*-base (weaken-∉ Γ₁ (Γ₂ , x ∶ τ) x τ' x-∉-Γ₁) in
  weaken*-trans weak-∅-Γ weak-Γ-x

-- For all context `Γ`, `Γ` is a reflexive-transitive weakening of the empty context `∅`.
weaken*-nil : ∀ Γ → Weaken* ∅ Γ
weaken*-nil Γ with length Γ
... | ⟨ _ , length-Γ ⟩ = weaken*-nil-length length-Γ

-- Preservation of inclusion under weakening, which means that if the context `Γ'`
-- is a weakening of the context `Γ`, and the assumption `x ∶ τ` is in `Γ`, then `x ∶ τ`
-- is in `Γ'`.
weaken-preserve-in : ∀ {Γ Γ' x τ}
  → Weaken Γ Γ'
  → x ∶ τ ∈ Γ
  → x ∶ τ ∈ Γ'
weaken-preserve-in {x = x} {τ} (weaken-∈ Γ₁ Γ₂ x' τ' τ₂ x'-∈-Γ₂) x-∈-Γ with in-concat-either-in-out Γ₁ Γ₂ x τ x-∈-Γ
... | inj₁ ⟨ x-∈-Γ₁ , x-∉-Γ₂ ⟩ =
  let x-≢-x' : x ≢ x'
      x-≢-x' = ≢-sym (in-out-distinct x'-∈-Γ₂ x-∉-Γ₂) in
  let x-∈-Γ' : x ∶ τ ∈ (Γ₁ , x' ∶ τ')
      x-∈-Γ' = ∈-i Γ₁ x τ x' τ' x-≢-x' x-∈-Γ₁ in
  in-out-in-concat x-∈-Γ' x-∉-Γ₂
... | inj₂ x-∈-Γ₂ = in-in-concat (Γ₁ , x' ∶ τ') x-∈-Γ₂
weaken-preserve-in {x = x} {τ} (weaken-∉ Γ₁ Γ₂ x' τ' x'-∉-Γ₁) x-∈-Γ with in-concat-either-in-out Γ₁ Γ₂ x τ x-∈-Γ
... | inj₁ ⟨ x-∈-Γ₁ , x-∉-Γ₂ ⟩ =
  let x-≢-x' : x ≢ x'
      x-≢-x' = in-out-distinct x-∈-Γ₁ x'-∉-Γ₁ in
  let x-∈-Γ' : x ∶ τ ∈ (Γ₁ , x' ∶ τ')
      x-∈-Γ' = ∈-i Γ₁ x τ x' τ' x-≢-x' x-∈-Γ₁ in
  in-out-in-concat x-∈-Γ' x-∉-Γ₂
... | inj₂ x-∈-Γ₂ = in-in-concat (Γ₁ , x' ∶ τ') x-∈-Γ₂

-- Preservation of typing under weakening, which means that if the context `Γ'`
-- is a weakening of the context `Γ`, and that the term `e` has type `τ` under `Γ`,
-- then `e` also has type `τ` under `Γ'`.
weaken-preserve-ty : ∀ {Γ Γ' e τ}
  → Weaken Γ Γ'
  → Γ ⊢ e ∶ τ
  → Γ' ⊢ e ∶ τ
weaken-preserve-ty _ ty-true =
  ty-true
weaken-preserve-ty _ ty-false =
  ty-false
weaken-preserve-ty {Γ' = Γ'} wk (ty-var {x = x} {τ} x-∈-Γ) =
  let x-∈-Γ' : x ∶ τ ∈ Γ'
      x-∈-Γ' = weaken-preserve-in wk x-∈-Γ in
  ty-var x-∈-Γ'
weaken-preserve-ty {Γ' = Γ'} wk (ty-if {τ = τ} {e₁} {e₂} {e₃} te₁ te₂ te₃) =
  let te₁' : Γ' ⊢ e₁ ∶ t-bool
      te₁' = weaken-preserve-ty wk te₁ in
  let te₂' : Γ' ⊢ e₂ ∶ τ
      te₂' = weaken-preserve-ty wk te₂ in
  let te₃' : Γ' ⊢ e₃ ∶ τ
      te₃' = weaken-preserve-ty wk te₃ in
  ty-if te₁' te₂' te₃'
weaken-preserve-ty {Γ' = Γ'} wk (ty-abs {Γ} {x} {e₂} {τ₁} {τ₂} te₂) =
  let wk' : Weaken (Γ , x ∶ τ₁) (Γ' , x ∶ τ₁)
      wk' = weaken-mono-ext x τ₁ wk in
  let te₂' : (Γ' , x ∶ τ₁) ⊢ e₂ ∶ τ₂
      te₂' = weaken-preserve-ty wk' te₂ in
  ty-abs te₂'
weaken-preserve-ty {Γ' = Γ'} wk (ty-app {e₁ = e₁} {e₂} {τ₁} {τ} te₁ te₂) =
  let te₁' : Γ' ⊢ e₁ ∶ t-abs τ₁ τ
      te₁' = weaken-preserve-ty wk te₁ in
  let te₂' : Γ' ⊢ e₂ ∶ τ₁
      te₂' = weaken-preserve-ty wk te₂ in
  ty-app te₁' te₂'

-- Preservation of typing under reflexive-transitive weakening.
weaken*-preserve-ty : ∀ {Γ Γ' e τ}
  → Weaken* Γ Γ'
  → Γ ⊢ e ∶ τ
  → Γ' ⊢ e ∶ τ
weaken*-preserve-ty (weaken*-refl Γ) te =
  te
weaken*-preserve-ty (weaken*-base e-Γ-Γ') te =
  weaken-preserve-ty e-Γ-Γ' te
weaken*-preserve-ty {e = e} {τ} (weaken*-trans {Γ} {Γ'} {Γ''} wk-Γ-Γ' wk-Γ'-Γ'') te =
  let te' : Γ' ⊢ e ∶ τ
      te' = weaken*-preserve-ty wk-Γ-Γ' te in
  weaken*-preserve-ty wk-Γ'-Γ'' te'
