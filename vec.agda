open import Data.Product using (_,_; ∃-syntax)
open import bool using (Bool; true; false)
open import nat using (ℕ; zero; succ; _+_)

data Vec (A : Set) : ℕ → Set where
  []   : Vec A zero
  _::_ : {n : ℕ} → A → Vec A n → Vec A (succ n)

_++_ : {A : Set} {m n : ℕ} → Vec A m → Vec A n → Vec A (m + n)
_++_ [] ys = ys
_++_ (x :: xs) ys = x :: (xs ++ ys)

head : {A : Set} {n : ℕ} → Vec A (succ n) → A
head (x :: _) = x

tail : {A : Set} {n : ℕ} → Vec A (succ n) → Vec A n
tail (_ :: xs) = xs 

map : {A B : Set} {n : ℕ} → (A → B) → Vec A n → Vec B n
map f []        = []
map f (x :: xs) = f x :: map f xs

filter : {A : Set} {n : ℕ} → (A → Bool) → Vec A n → ∃[ m ] Vec A m 
filter f [] = zero , []
filter f (x :: xs) with filter f xs
... | n , xs' with f x
... | true  = succ n , x :: xs' 
... | false = n , xs'
