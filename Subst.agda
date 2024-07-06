open import Data.Product using (∃-syntax) renaming (_,_ to ⟨_,_⟩)
open import Data.String.Properties using (_≟_)
open import Data.String using (String)
open import Relation.Binary.PropositionalEquality using (_≢_)
open import Relation.Nullary using (yes; no)

open import Syntax

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
