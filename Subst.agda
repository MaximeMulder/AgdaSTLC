open import Data.String using (String)
open import Relation.Binary.PropositionalEquality using (_≢_)

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
