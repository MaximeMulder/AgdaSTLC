open import Data.Product using (∃-syntax) renaming (_,_ to ⟨_,_⟩)
open import Data.String.Properties using (_≟_)
open import Data.String using (String)
open import Relation.Binary.PropositionalEquality using (_≢_; sym; ≢-sym)
open import Relation.Nullary using (yes; no)

open import Ctx
open import Contract
open import Exchange
open import Syntax
open import Typing
open import Weaken

-- Term substitution, which is the replacement of all occurrences of a given
-- variable in a term by another term.
data _[_/_]⇛_ : Term → Term → String → Term → Set where
  subst-true : ∀ x eₓ
    → tm-true [ eₓ / x ]⇛ tm-true
  subst-false : ∀ x eₓ
    → tm-false [ eₓ / x ]⇛ tm-false
  subst-var-eq : ∀ x eₓ
    → (tm-var x) [ eₓ / x ]⇛ eₓ
  subst-var-ne : ∀ x eₓ y
    → x ≢ y
    → (tm-var y) [ eₓ / x ]⇛ (tm-var y)
  subst-if : ∀ x eₓ e₁ e₂ e₃ e₁' e₂' e₃'
    → e₁ [ eₓ / x ]⇛ e₁'
    → e₂ [ eₓ / x ]⇛ e₂'
    → e₃ [ eₓ / x ]⇛ e₃'
    → (tm-if e₁ e₂ e₃) [ eₓ / x ]⇛ (tm-if e₁' e₂' e₃')
  subst-abs-eq : ∀ x eₓ τ e
    → (tm-abs x τ e) [ eₓ / x ]⇛ (tm-abs x τ e)
  subst-abs-ne : ∀ x eₓ y τ e e'
    → x ≢ y
    → e [ eₓ / x ]⇛ e'
    → (tm-abs y τ e) [ eₓ / x ]⇛ (tm-abs y τ e')
  subst-app : ∀ x eₓ e₁ e₂ e₁' e₂'
    → e₁ [ eₓ / x ]⇛ e₁'
    → e₂ [ eₓ / x ]⇛ e₂'
    → (tm-app e₁ e₂) [ eₓ / x ]⇛ (tm-app e₁' e₂')

-- Substitution is total, which means that for any term `e`,  variable `x` and
-- substitute `eₓ`, there exists a term `e'` that is a substitution of `x`
-- by `eₓ` in `e`.
subst-total : ∀ e x eₓ → ∃[ e' ] (e [ eₓ / x ]⇛ e')
subst-total tm-true x eₓ = ⟨ tm-true , subst-true x eₓ ⟩
subst-total tm-false x eₓ = ⟨ tm-false , subst-false x eₓ ⟩
subst-total (tm-var y) x eₓ with x ≟ y
... | yes x-≡-y rewrite x-≡-y = ⟨ eₓ , subst-var-eq y eₓ ⟩
... | no  x-≢-y = ⟨ tm-var y , subst-var-ne x eₓ y x-≢-y ⟩
subst-total (tm-if e₁ e₂ e₃) x eₓ with subst-total e₁ x eₓ | subst-total e₂ x eₓ | subst-total e₃ x eₓ
... | ⟨ e₁' , se₁ ⟩ | ⟨ e₂' , se₂ ⟩ | ⟨ e₃' , se₃ ⟩ =
  ⟨ tm-if e₁' e₂' e₃' , subst-if x eₓ e₁ e₂ e₃ e₁' e₂' e₃' se₁ se₂ se₃ ⟩
subst-total (tm-abs y τ e) x eₓ with x ≟ y
... | yes x-≡-y rewrite x-≡-y =
  ⟨ tm-abs y τ e , subst-abs-eq y eₓ τ e ⟩
... | no  x-≢-y with subst-total e x eₓ
... | ⟨ e' , se' ⟩ =
  ⟨ tm-abs y τ e' , subst-abs-ne x eₓ y τ e e' x-≢-y se' ⟩
subst-total (tm-app e₁ e₂) x eₓ with subst-total e₁ x eₓ | subst-total e₂ x eₓ
... | ⟨ e₁' , se₁ ⟩ | ⟨ e₂' , se₂ ⟩ =
  ⟨ tm-app e₁' e₂' , subst-app x eₓ e₁ e₂ e₁' e₂' se₁ se₂ ⟩

-- Preservation of typing under substitution, which means that if a term `e`
-- has type `τ` under a context `Γ` where the assumption `x ∶ τₓ` is in this
-- context, then `e` also has type `τ` under `Γ` without `x`.
-- TODO: This definition needs to be generalized to match the above comment.
-- "`Γ` without `x`" is also not properly defined. Maybe I should define a
-- deletion operation ?
subst-preserve-ty : ∀ Γ x eₓ τₓ e τ e'
  → ∅ ⊢ eₓ ∶ τₓ
  → (Γ , x ∶ τₓ) ⊢ e ∶ τ
  → e [ eₓ / x ]⇛ e'
  → Γ ⊢ e' ∶ τ
subst-preserve-ty Γ x eₓ τₓ e τ e' _ (t-true (Γ , x ∶ τₓ)) (subst-true x eₓ) =
  t-true Γ
subst-preserve-ty Γ x eₓ τₓ e τ e' _ (t-false (Γ , x ∶ τₓ)) (subst-false x eₓ) =
  t-false Γ
subst-preserve-ty Γ x eₓ τₓ e τ e' teₓ (t-var (Γ , x ∶ τₓ) x τ x-∈-Γ) (subst-var-eq x eₓ) rewrite sym (in-unique (Γ , x ∶ τₓ) x τ τₓ x-∈-Γ (∈-b Γ x τₓ)) =
  weaken*-preserve-ty ∅ Γ eₓ τ (weaken*-nil Γ) teₓ
subst-preserve-ty Γ x eₓ τₓ e τ e' teₓ (t-var (Γ , x ∶ τₓ) x' τ x'-∈-Γ) (subst-var-ne x eₓ x' x-≢-x') =
  let x'-∈-Γ : x' ∶ τ ∈ Γ
      x'-∈-Γ = in-ext-distinct-in Γ x' τ x τₓ (≢-sym x-≢-x') x'-∈-Γ in
  t-var Γ x' τ x'-∈-Γ
subst-preserve-ty Γ x eₓ τₓ e τ e' teₓ (t-if (Γ , x ∶ τₓ) τ e₁ e₂ e₃ te₁ te₂ te₃) (subst-if x eₓ e₁ e₂ e₃ e₁' e₂' e₃' se₁' se₂' se₃') =
  let te₁' : Γ  ⊢ e₁' ∶ ty-bool
      te₁' = subst-preserve-ty Γ x eₓ τₓ e₁ ty-bool e₁' teₓ te₁ se₁' in
  let te₂' : Γ  ⊢ e₂' ∶ τ
      te₂' = subst-preserve-ty Γ x eₓ τₓ e₂ τ e₂' teₓ te₂ se₂' in
  let te₃' : Γ  ⊢ e₃' ∶ τ
      te₃' = subst-preserve-ty Γ x eₓ τₓ e₃ τ e₃' teₓ te₃ se₃' in
  t-if Γ τ e₁' e₂' e₃' te₁' te₂' te₃'
subst-preserve-ty Γ x eₓ τₓ e τ e' teₓ (t-abs (Γ , x ∶ τₓ) x e₂ τ₁ τ₂ te₂) (subst-abs-eq x eₓ τ₁ e₂) =
  let c : Contract (Γ , x ∶ τₓ , x ∶ τ₁) (Γ , x ∶ τ₁)
      c = contract Γ (∅ , x ∶ τ₁) x τₓ τ₁ (∈-b ∅ x τ₁) in
  t-abs Γ x e₂ τ₁ τ₂ (contract-preserve-ty (Γ , x ∶ τₓ , x ∶ τ₁) (Γ , x ∶ τ₁) e₂ τ₂ c te₂)
subst-preserve-ty Γ x eₓ τₓ e τ e' teₓ (t-abs (Γ , x ∶ τₓ) x₁ e₂ τ₁ τ₂ te₂) (subst-abs-ne x eₓ x₁ τ₁ e₂ e₂' x-≢-x₁ se₂) =
  let ex : Exchange (Γ , x ∶ τₓ , x₁ ∶ τ₁) (Γ , x₁ ∶ τ₁ , x ∶ τₓ)
      ex = exchange Γ ∅ x τₓ x₁ τ₁ x-≢-x₁ in
  let te₂' : Γ , x₁ ∶ τ₁ , x ∶ τₓ ⊢ e₂ ∶ τ₂
      te₂' = exchange-preserve-ty (Γ , x ∶ τₓ , x₁ ∶ τ₁) (Γ , x₁ ∶ τ₁ , x ∶ τₓ) e₂ τ₂ ex te₂ in
  let te₂'' : Γ , x₁ ∶ τ₁ ⊢ e₂' ∶ τ₂
      te₂'' = subst-preserve-ty (Γ , x₁ ∶ τ₁) x eₓ τₓ e₂ τ₂ e₂' teₓ te₂' se₂ in
  t-abs Γ x₁ e₂' τ₁ τ₂ te₂''
subst-preserve-ty Γ x eₓ τₓ e τ e' teₓ (t-app (Γ , x ∶ τₓ) e₁ e₂ τ₁ τ₂ te₁ te₂) (subst-app x eₓ e₁ e₂ e₁' e₂' se₁ se₂) =
  let te₁' : Γ ⊢ e₁' ∶ ty-abs τ₁ τ₂
      te₁' = subst-preserve-ty Γ x eₓ τₓ e₁ (ty-abs τ₁ τ₂) e₁' teₓ te₁ se₁ in
  let te₂' : Γ ⊢ e₂' ∶ τ₁
      te₂' = subst-preserve-ty Γ x eₓ τₓ e₂ τ₁ e₂' teₓ te₂ se₂ in
  t-app Γ e₁' e₂' τ₁ τ₂ te₁' te₂'
