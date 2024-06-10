open import Agda.Builtin.String

data Type : Set where
  bool : Type
  lam  : Type -> Type -> Type

data Term : Set where
  true  : Term
  false : Term
  var   : String -> Term
  abs   : String -> Type -> Term
  app   : Term -> Term -> Term
  if    : Term -> Term -> Term -> Term

Γ = List Type
Id = ℕ

data Typed : (E : Term) (T : Type) → Set  where
  t-true  : Typed true  bool
  t-false : Typed false bool
  t-app   : (t-1 : Type) → (t-2 : Type) → (e-1 : Term) → (e-2 : Term)
    → (Typed e-1 (lam t-1 t-2))
    → (Typed e-2 t-2)
    → Typed (app e-1 e-2) (t-2)
  t-if    : (t : Type) → (e-1 : Term) → (e-2 : Term) → (e-3 : Term)
    → Typed e-1 bool
    → Typed e-2 t
    → Typed e-3 t
    → Typed (if e-1 e-2 e-3) t

{- https://www.cse.chalmers.se/~ulfn/papers/afp08/tutorial.pdf -}

data Bool : Set where
  true  : Bool
  false : Bool

not : Bool → Bool
not true  = false
not false = true

infixl 30 _and_
infixl 20 _or_
infix  5  if_then_else_

_or_ : Bool → Bool → Bool
false or y = y
true  or y = true

_and_ : Bool → Bool → Bool
true  and y = true
false and y = y

if_then_else_ : {A : Set} → Bool → A → A → A
if true  then x else _ = x
if false then _ else y = y

data Nat : Set where
  zero : Nat
  succ : Nat → Nat

infixl 60 _*_
infixl 40 _+_

_+_ : Nat → Nat → Nat
zero   + m = m
succ n + m = succ (n + m)

_*_ : Nat → Nat → Nat
zero   * m = zero
succ n * m = m + n * m

infixl 35 _::_

data List (A : Set) : Set where
   []   : List A
   _::_ : A → List A → List A

identity : {A : Set} → A → A
identity x = x

map : {A B : Set} → (A → B) → List(A) → List(B)
map f []        = []
map f (x :: xs) = f x :: map f xs

_++_ : {A : Set} → List(A) → List(A) → List(A)
[]        ++ ys = ys
(x :: xs) ++ ys = x :: (xs ++ ys)

data Vec (A : Set) : Nat → Set where
  []   : Vec A zero
  _::_ : {n : Nat} → A → Vec A n → Vec A (succ n)

vhead : {A : Set} {n : Nat} → Vec A (succ n) → A
vhead (x :: _) = x

vmap : {A B : Set} {n : Nat} → (A → B) → Vec A n → Vec B n
vmap f []        = []
vmap f (x :: xs) = f x :: vmap f xs
