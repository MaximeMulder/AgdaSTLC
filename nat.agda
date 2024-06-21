import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)

data ℕ : Set where
  zero : ℕ
  succ : ℕ → ℕ

infixl 22 _×_
infixl 21 _+_ _∸_

_+_ : ℕ → ℕ → ℕ
zero   + m = m
succ n + m = succ (n + m)

_∸_ : ℕ → ℕ → ℕ
zero   ∸ m      = zero
n      ∸ zero   = n
succ n ∸ succ m = n ∸ m

_×_ : ℕ → ℕ → ℕ
zero   × m = zero
succ n × m = m + n × m

-- Zero is a right-identity for the addition
-- (the left-identity is true by definition)
+-ident : (m : ℕ) → m + zero ≡ m
+-ident zero =
  begin
    zero + zero
  ≡⟨⟩
    zero
  ∎
+-ident (succ m) =
  begin
    succ (m + zero)
  ≡⟨⟩
    succ m + zero
  ≡⟨ cong succ (+-ident m) ⟩
    succ m
  ∎

-- Addition does things with its right successor
+-succ : (m n : ℕ) → m + succ n ≡ succ (m + n)
+-succ zero n =
  begin
    zero + succ n
  ≡⟨⟩
    succ n
  ≡⟨⟩
    succ (zero + n)
  ∎
+-succ (succ m) n =
  begin
    succ m + succ n
  ≡⟨⟩
    succ (m + succ n)
  ≡⟨ cong succ (+-succ m n) ⟩
    succ (succ (m + n))
  ∎

-- Addition is commutative
+-comm : (m n : ℕ) → m + n ≡ n + m
+-comm m zero =
  begin
    m + zero
  ≡⟨ +-ident m ⟩
    m
  ≡⟨⟩
    zero + m
  ∎
+-comm m (succ n) =
  begin
    m + succ n
  ≡⟨ +-succ m n ⟩
    succ (m + n)
  ≡⟨ cong succ (+-comm m n) ⟩
    succ (n + m)
  ≡⟨⟩
    succ n + m
  ∎

-- Addition is associative
+-assoc : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
+-assoc zero n p =
  begin
    (zero + n) + p
  ≡⟨⟩
    n + p
  ≡⟨⟩
    zero + (n + p)
  ∎
+-assoc (succ m) n p =
  begin
    (succ m + n) + p
  ≡⟨⟩
    succ (m + n) + p
  ≡⟨⟩
    succ ((m + n) + p)
  ≡⟨ cong succ (+-assoc m n p) ⟩
    succ (m + (n + p))
  ≡⟨⟩
    succ m + (n + p)
  ∎
