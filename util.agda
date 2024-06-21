data Either (A : Set) (B : Set) : Set where
  l : A → Either A B
  r : B → Either A B
