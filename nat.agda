import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)
open import util using (Either; l; r)

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

data _≤_ : ℕ → ℕ → Set where
  ≤-zero : (n : ℕ)
    → zero ≤ n
  ≤-succ : ∀ {m n : ℕ}
    → m ≤ n
    → succ m ≤ succ n

-- Inequality is reflexive
≤-refl : (n : ℕ) → n ≤ n
≤-refl zero = ≤-zero zero
≤-refl (succ n) = ≤-succ (≤-refl n)

-- Inequality is transitive
≤-trans : {m n p : ℕ} → m ≤ n → n ≤ p → m ≤ p
≤-trans {_} {_} {p} (≤-zero n) _ = ≤-zero p
≤-trans (≤-succ m≤n) (≤-succ n≤p) = ≤-succ (≤-trans m≤n n≤p)

-- Inequality is anti-symmetric
≤-anti-sym : {m n : ℕ} → m ≤ n → n ≤ m → m ≡ n
≤-anti-sym (≤-zero n) (≤-zero m) = refl
≤-anti-sym (≤-succ m≤n) (≤-succ n≤m) = cong succ (≤-anti-sym m≤n n≤m)

-- Inequality is total
≤-total : (m n : ℕ) → Either (m ≤ n) (n ≤ m)
≤-total zero n = l (≤-zero n)
≤-total m zero = r (≤-zero m)
≤-total (succ m) (succ n) with ≤-total m n
... | l m≤n = l (≤-succ m≤n)
... | r n≤m = r (≤-succ n≤m)

-- Addition is monotonic with regard to inequality
+-≤-mono-r : (m n p : ℕ) → n ≤ p → m + n ≤ m + p
+-≤-mono-r zero n p n≤p = n≤p
+-≤-mono-r (succ m) n p n≤p = ≤-succ (+-≤-mono-r m n p n≤p)

-- NGL I have no idea how this proof works
+-≤-mono-l : (m n p : ℕ) → m ≤ n → m + p ≤ n + p
+-≤-mono-l m n p m≤n rewrite +-comm m p | +-comm n p = +-≤-mono-r p m n m≤n

-- This one either...
+-≤-mono : (m n p q : ℕ) → m ≤ n → p ≤ q → m + p ≤ n + q
+-≤-mono m n p q m≤n p≤q = ≤-trans (+-≤-mono-l m n p m≤n) (+-≤-mono-r n p q p≤q)

data _<_ : ℕ → ℕ → Set where
  <-zero : (n : ℕ)
    → zero < (succ n)
  <-succ : {m n : ℕ}
    → m < n
    → succ m < succ n

-- Do some exercises here

data even : ℕ → Set
data odd  : ℕ → Set

data even where
  even-zero : even zero
  even-succ : (n : ℕ)
    → odd n
    → even (succ n)

data odd where
  odd-succ : (n : ℕ)
    → even n
    → odd (succ n)

-- Do some other exercises here
