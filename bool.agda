open import Relation.Binary.PropositionalEquality using (_≡_; refl)

data Bool : Set where
  true  : Bool
  false : Bool

¬_ : Bool → Bool
¬ true  = false
¬ false = true

_∨_ : Bool → Bool → Bool
false ∨ y = y
true  ∨ y = true

_∧_ : Bool → Bool → Bool
true  ∧ y = true
false ∧ y = y

if_then_else_ : {A : Set} → Bool → A → A → A
if true  then x else _ = x
if false then _ else y = y

infixl 23 _∧_
infixl 22 _∨_
infix  21 if_then_else_

-- NGL I have no idea how refl works, so this might be ugly (especially the last one)

p-if-true : {a b : Bool} → (if true then a else b) ≡ a
p-if-true = refl

p-if-false : {a b : Bool} → (if false then a else b) ≡ b
p-if-false = refl

p-distrib-1 : (a b c : Bool) → a ∧ (b ∨ c) ≡ (a ∧ b) ∨ (a ∧ c)
p-distrib-1 true  true  true  = refl
p-distrib-1 true  true  false = refl
p-distrib-1 true  false true  = refl
p-distrib-1 true  false false = refl
p-distrib-1 false true  true  = refl
p-distrib-1 false true  false = refl
p-distrib-1 false false true  = refl
p-distrib-1 false false false = refl
