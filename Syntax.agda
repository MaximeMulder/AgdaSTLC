open import Data.String using (String)

data Type : Set where
  t-bool : Type
  t-abs  : Type → Type → Type

data Term : Set where
  e-true  : Term
  e-false : Term
  e-var   : String →  Term
  e-abs   : String → Type → Term → Term
  e-app   : Term → Term → Term
  e-if    : Term → Term → Term → Term
