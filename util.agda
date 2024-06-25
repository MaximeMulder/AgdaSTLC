-- Inferior alternatives to Data.Product and Data.Sum !!!

data Either (A : Set) (B : Set) : Set where
  l : A → Either A B
  r : B → Either A B

data Pair (A : Set) (B : Set) : Set where
  pair : A → B → Pair A B
