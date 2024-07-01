open import Data.String using (String)

data Type : Set where
  ty-bool : Type
  ty-abs  : Type → Type → Type

data Term : Set where
  tm-true  : Term
  tm-false : Term
  tm-var   : String →  Term
  tm-abs   : String → Type → Term → Term
  tm-app   : Term → Term → Term
  tm-if    : Term → Term → Term → Term
