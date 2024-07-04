open import Data.Product using (_×_) renaming (_,_ to ⟨_,_⟩)
open import Data.String.Properties using (_≟_)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; sym; ≢-sym)
open import Relation.Nullary using (yes; no)

open import Ctx

-- Context weakening, usually abbreviated as "weaken", which is the insertion
-- of an assumption in a context that does not invalidate any assumption of this
-- context.
data Weaken : Ctx → Ctx → Set where
  weaken-∉ : ∀ Γ₁ Γ₂ x τ
    → x ∉ Γ₁
    → Weaken (Γ₁ , Γ₂) (Γ₁ , x ∶ τ , Γ₂)
  weaken-∈ : ∀ Γ₁ Γ₂ x τ τ₂
    → x ∶ τ₂ ∈ Γ₂
    → Weaken (Γ₁ , Γ₂) (Γ₁ , x ∶ τ , Γ₂)

-- Reflexive transitive closure of the context extension.
-- TODO: Factorize with the standard library
data Weaken*  : Ctx → Ctx → Set where
  weaken*-base : ∀ Γ Γ'
    → Weaken Γ Γ'
    → Weaken* Γ Γ'
  weaken*-refl : ∀ Γ
    → Weaken* Γ Γ
  weaken*-trans : ∀ Γ Γ' Γ''
    → Weaken* Γ Γ'
    → Weaken* Γ' Γ''
    → Weaken* Γ Γ''

-- Monotonicity of weakening under extension, which means that if `Γ'` is a
-- weakening of `Γ`, then the extension of `Γ'` with the assumption `x ∶ τ` is a
-- weakening of the extension of `Γ` with `x ∶ τ`.
weaken-mono-ext : ∀ Γ Γ' x τ
  → Weaken Γ Γ'
  → Weaken (Γ , x ∶ τ) (Γ' , x ∶ τ)
weaken-mono-ext _ _ x τ (weaken-∉ Γ₁ Γ₂ x' τ' x'-∉-Γ₁) =
  weaken-∉ Γ₁ (Γ₂ , x ∶ τ) x' τ' x'-∉-Γ₁
weaken-mono-ext _ _ x τ (weaken-∈ Γ₁ Γ₂ x' τ' τ₂ x'-∈-Γ₂) with x ≟ x'
... | yes x-≡-x' rewrite sym x-≡-x' = weaken-∈ Γ₁ (Γ₂ , x ∶ τ) x τ' τ (∈-b Γ₂ x τ)
... | no  x-≢-x' = weaken-∈ Γ₁ (Γ₂ , x ∶ τ) x' τ' τ₂ (∈-i Γ₂ x' τ₂ x τ (≢-sym x-≢-x') x'-∈-Γ₂)

postulate
  weaken*-concat-nil-ext : ∀ Γ x τ
    → Weaken* ∅ Γ
    → Weaken* ∅ (∅ , x ∶ τ)
    → Weaken* ∅ (Γ , x ∶ τ)

-- Any context `Γ` is a weakening of the empty context `∅`.
weaken*-nil : ∀ Γ → Weaken* ∅ Γ
weaken*-nil ∅ = weaken*-refl ∅
weaken*-nil (Γ , x ∶ τ) =
  let weak-Γ : Weaken* ∅ Γ
      weak-Γ = weaken*-nil Γ in
  let weak-x : Weaken* ∅ (∅ , x ∶ τ)
      weak-x = weaken*-base ∅ (∅ , x ∶ τ) (weaken-∉ ∅ ∅ x τ (∉-b x)) in
  let ∅-Γ-≡-Γ : (∅ , Γ , (∅ , x ∶ τ)) ≡ Γ , x ∶ τ
      ∅-Γ-≡-Γ = concat-ident-l (Γ , (∅ , x ∶ τ)) in
  weaken*-concat-nil-ext Γ x τ weak-Γ weak-x

-- Preservation of inclusion under weakening, which means that if the context `Γ'`
-- is a weakening of the context `Γ`, and the assumption `x ∶ τ` is in `Γ`, then `x ∶ τ`
-- is in `Γ'`.
weaken-preserve-in : ∀ Γ Γ' x τ
  → Weaken Γ Γ'
  → x ∶ τ ∈ Γ
  → x ∶ τ ∈ Γ'
weaken-preserve-in Γ Γ' x τ (weaken-∈ Γ₁ Γ₂ x' τ' τ₂ x'-∈-Γ₂) x-∈-Γ with in-concat-either-in-out Γ₁ Γ₂ x τ x-∈-Γ
... | inj₁ ⟨ x-∈-Γ₁ , x-∉-Γ₂ ⟩ =
  let x-≢-x' : x ≢ x'
      x-≢-x' = ≢-sym (in-out-distinct Γ₂ x' x τ₂ x'-∈-Γ₂ x-∉-Γ₂) in
  let x-∈-Γ' : x ∶ τ ∈ (Γ₁ , x' ∶ τ')
      x-∈-Γ' = ∈-i Γ₁ x τ x' τ' x-≢-x' x-∈-Γ₁ in
  in-out-in-concat (Γ₁ , x' ∶ τ') Γ₂ x τ x-∈-Γ' x-∉-Γ₂
... | inj₂ x-∈-Γ₂ = in-in-concat (Γ₁ , x' ∶ τ') Γ₂ x τ x-∈-Γ₂
weaken-preserve-in Γ Γ' x τ (weaken-∉ Γ₁ Γ₂ x' τ' x'-∉-Γ₁) x-∈-Γ with in-concat-either-in-out Γ₁ Γ₂ x τ x-∈-Γ
... | inj₁ ⟨ x-∈-Γ₁ , x-∉-Γ₂ ⟩ =
  let x-≢-x' : x ≢ x'
      x-≢-x' = in-out-distinct Γ₁ x x' τ x-∈-Γ₁ x'-∉-Γ₁ in
  let x-∈-Γ' : x ∶ τ ∈ (Γ₁ , x' ∶ τ')
      x-∈-Γ' = ∈-i Γ₁ x τ x' τ' x-≢-x' x-∈-Γ₁ in
  in-out-in-concat (Γ₁ , x' ∶ τ') Γ₂ x τ x-∈-Γ' x-∉-Γ₂
... | inj₂ x-∈-Γ₂ = in-in-concat (Γ₁ , x' ∶ τ') Γ₂ x τ x-∈-Γ₂
