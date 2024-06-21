open import Agda.Builtin.String

{- https://www.cse.chalmers.se/~ulfn/papers/afp08/tutorial.pdf -}

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

open import Data.Product using (∃; ∃-syntax)

vfilter : {A : Set} {n : Nat} → (A → Bool) → Vec A n → ∃[ m ] Vec A m
vfilter f [] = []
vfilter f (x :: xs) with f x
... | true  = x :: (vfilter f xs)
... | false = vfilter f xs
