open import Data.Nat using (suc)
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
weaken-mono-ext : ∀ Γ Γ' x τ
  → Weaken Γ Γ'
  → Weaken (Γ , x ∶ τ) (Γ' , x ∶ τ)
weaken-mono-ext _ _ x τ (weaken-∉ Γ₁ Γ₂ x' τ' x'-∉-Γ₁) =
  weaken-∉ Γ₁ (Γ₂ , x ∶ τ) x' τ' x'-∉-Γ₁
weaken-mono-ext _ _ x τ (weaken-∈ Γ₁ Γ₂ x' τ' τ₂ x'-∈-Γ₂) with x ≟ x'
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
      length-Γ' = length-ext-concat Γ₁ (Γ₂ , x ∶ τ) x τ' n (length-suc (Γ₁ , x ∶ τ' , Γ₂) n x τ length-Γ) in
  let weak-∅-Γ : Weaken* ∅ (Γ₁ , (Γ₂ , x ∶ τ))
      weak-∅-Γ = weaken*-nil-length length-Γ' in
  let weak-Γ-x : Weaken* (Γ₁ , (Γ₂ , x ∶ τ)) ((Γ₁ , x ∶ τ') , (Γ₂ , x ∶ τ))
      weak-Γ-x = weaken*-base (weaken-∉ Γ₁ (Γ₂ , x ∶ τ) x τ' x-∉-Γ₁) in
  weaken*-trans weak-∅-Γ weak-Γ-x

weaken*-nil : ∀ Γ → Weaken* ∅ Γ
weaken*-nil Γ with length Γ
... | ⟨ _ , length-Γ ⟩ = weaken*-nil-length length-Γ

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
