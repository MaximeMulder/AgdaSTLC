open import bool using (Bool; true; false)

data List (A : Set) : Set where
   []   : List A
   _::_ : A → List A → List A

_++_ : {A : Set} → List A → List A → List A
[]        ++ ys = ys
(x :: xs) ++ ys = x :: (xs ++ ys)

map : {A B : Set} → (A → B) → List A → List B
map f []        = []
map f (x :: xs) = f x :: map f xs

filter : {A : Set} → (A → Bool) → List A → List A
filter f [] = []
filter f (x :: xs) with f x
... | true  = x :: filter f xs
... | false =      filter f xs
