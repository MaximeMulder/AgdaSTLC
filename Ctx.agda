open import Data.Product using (_×_) renaming (_,_ to ⟨_,_⟩)
open import Data.String using (String)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; cong; refl; sym; ≢-sym)
open import Relation.Nullary.Negation using (contradiction)

open import Syntax

infixl 21 _,_
infixl 21 _,_∶_
infix 20 _∶_∈_
infix 20 _∉_

-- The typing context, commonly referred as the "context".
data Ctx : Set  where
  -- The empty context, sometimes referred as "nil".
  ∅ : Ctx
  -- The context extension, sometimes referred as "ext".
  _,_∶_ : Ctx → String → Type → Ctx

-- The context concatenation.
_,_ : Ctx → Ctx → Ctx
Γ , ∅ = Γ
Γ , (Γ' , x ∶ τ) = (Γ , Γ') , x ∶ τ

-- The empty context `∅` is a left identity of the context concatenation.
-- The right identity is true by definition.
concat-ident-l : ∀ Γ → ∅ , Γ ≡ Γ
concat-ident-l ∅ =
  refl
concat-ident-l (Γ , x ∶ τ) =
  cong (λ Γ → Γ , x ∶ τ) (concat-ident-l Γ)

-- Commutativity of context concatenation under extension.
concat-comm-ext : ∀ Γ Γ' x τ → (Γ , x ∶ τ , Γ') ≡ Γ , (∅ , x ∶ τ , Γ')
concat-comm-ext Γ ∅ x τ =
  refl
concat-comm-ext Γ (Γ' , _ ∶ _) x τ rewrite concat-comm-ext Γ Γ' x τ =
  refl

-- Commutativity of context concatenation.
concat-comm : ∀ Γ₁ Γ₂ Γ₃ → (Γ₁ , Γ₂) , Γ₃ ≡ Γ₁ , (Γ₂ , Γ₃)
concat-comm Γ₁ ∅ Γ₃ rewrite concat-ident-l Γ₃ =
  refl
concat-comm Γ₁ (Γ₂ , x ∶ τ) Γ₃ rewrite concat-comm-ext (Γ₁ , Γ₂) Γ₃ x τ  | concat-comm Γ₁ Γ₂ (∅ , x ∶ τ , Γ₃) | sym (concat-comm-ext Γ₂ Γ₃ x τ) =
  refl

-- The inclusion of an entry in a context, or "in", relation.
data _∶_∈_ : String → Type → Ctx → Set where
  ∈-b : ∀ Γ x τ
    → x ∶ τ ∈ Γ , x ∶ τ
  ∈-i : ∀ Γ x τ x' τ'
    → x ≢ x'
    → x ∶ τ ∈ Γ
    → x ∶ τ ∈ Γ , x' ∶ τ'

-- The exclusion of a variable in a context, or "out", relation.
data _∉_ : String → Ctx → Set where
  ∉-b : ∀ x
    → x ∉ ∅
  ∉-i : ∀ Γ x x' τ'
    → x ≢ x'
    → x ∉ Γ
    → x ∉ Γ , x' ∶ τ'

-- If a variable `x` is in the context `Γ`, and a variable `y` is not in `Γ`,
-- then `x` and `y` are distinct.
in-out-distinct : ∀ Γ x y τ
  → x ∶ τ ∈ Γ
  → y ∉ Γ
  → x ≢ y
in-out-distinct ∅ x y τ ()
in-out-distinct (Γ , x ∶ τ) x y τ (∈-b Γ x τ) (∉-i Γ y x τ ≢-yx _) =
  ≢-sym ≢-yx
in-out-distinct (Γ , x' ∶ τ') x y τ (∈-i Γ x τ x' τ' _ ∈-x-Γ) (∉-i Γ y x' τ' _ ∉-y-Γ) =
  in-out-distinct Γ x y τ ∈-x-Γ ∉-y-Γ

-- If the entry `x ∶ τ` is in the concatenation of the contexts `Γ₁` and `Γ₂`,
-- then either `x ∶ τ` is in `Γ₁` and `x` is out of `Γ₂`, or `x ∶ τ` is in `Γ₂`.
in-concat-either-in-out : ∀ Γ₁ Γ₂ x τ
  → x ∶ τ ∈ Γ₁ , Γ₂
  → x ∶ τ ∈ Γ₁ × x ∉ Γ₂ ⊎ x ∶ τ ∈ Γ₂
in-concat-either-in-out Γ₁ ∅ x τ x-∈-Γ₁ =
  inj₁ ⟨ x-∈-Γ₁ , ∉-b x ⟩
in-concat-either-in-out Γ₁ (Γ₂ , x₂ ∶ τ₂) x τ (∈-b Γ x τ) =
  inj₂ (∈-b Γ₂ x τ)
in-concat-either-in-out Γ₁ (Γ₂ , x₂ ∶ τ₂) x τ (∈-i Γ x τ x₂ τ₂ x-≢-x₂ x-∈-Γ) with in-concat-either-in-out Γ₁ Γ₂ x τ x-∈-Γ
... | inj₁ ⟨ x-∈-Γ₁ , x-∉-Γ₂ ⟩ = inj₁ ⟨ x-∈-Γ₁ , ∉-i Γ₂ x x₂ τ₂ x-≢-x₂ x-∉-Γ₂ ⟩
... | inj₂ x-∈-Γ₂ = inj₂ (∈-i Γ₂ x τ x₂ τ₂ x-≢-x₂ x-∈-Γ₂)

-- If the entry `x ∶ τ` is in the context `Γ₁`, and `x` is out of the context `Γ₂`,
-- then `x ∶ τ` is in the concatenation of `Γ₁` and `Γ₂`.
in-out-in-concat : ∀ Γ₁ Γ₂ x τ
  → x ∶ τ ∈ Γ₁
  → x ∉ Γ₂
  → x ∶ τ ∈ Γ₁ , Γ₂
in-out-in-concat Γ₁ ∅ x τ x-∈-Γ₁ x-∉-Γ₂ = x-∈-Γ₁
in-out-in-concat Γ₁ (Γ₂ , x₂ ∶ τ₂) x τ x-∈-Γ₁ (∉-i Γ₂ x x₂ τ₂ x-≢-x₂ x-∉-Γ₂) =
  let x-∈-Γ' : x ∶ τ ∈ (Γ₁ , Γ₂)
      x-∈-Γ' = in-out-in-concat Γ₁ Γ₂ x τ x-∈-Γ₁ x-∉-Γ₂ in
  ∈-i (Γ₁ , Γ₂) x τ x₂ τ₂ x-≢-x₂ x-∈-Γ'

-- If the entry `x ∶ τ` is in the context `Γ`, then `x ∶ τ` is in the concatenation
-- of the extension of the empty context `∅` with the entry `x' ∶ τ'` and `Γ`.
in-in-nil-ext-concat : ∀ Γ x τ x' τ'
  → x ∶ τ ∈ Γ
  → x ∶ τ ∈ ∅ , x' ∶ τ' , Γ
in-in-nil-ext-concat (Γ , x ∶ τ) x τ x' τ' (∈-b Γ x τ) =
  ∈-b (∅ , x' ∶ τ' , Γ) x τ
in-in-nil-ext-concat (Γ , x'' ∶ τ'') x τ x' τ' (∈-i Γ x τ x'' τ'' x-≢-x'' x-∈-Γ) =
  let x-∈-Γ' : x ∶ τ ∈ (∅ , x' ∶ τ' , Γ)
      x-∈-Γ' = in-in-nil-ext-concat Γ x τ x' τ' x-∈-Γ in
  ∈-i (∅ , x' ∶ τ' , Γ) x τ x'' τ'' x-≢-x'' x-∈-Γ'

-- If the entry `x ∶ τ` is in the context `Γ₂`, then `x ∶ τ` is in the concatenation
-- of the context `Γ₁` and `Γ₂`.
in-in-concat : ∀ Γ₁ Γ₂ x τ
  → x ∶ τ ∈ Γ₂
  → x ∶ τ ∈ Γ₁ , Γ₂
in-in-concat ∅ Γ₂ x τ (∈-b Γ₂' x τ) rewrite concat-ident-l Γ₂' =
  ∈-b Γ₂' x τ
in-in-concat ∅ (Γ₂ , x₂ ∶ τ₂) x τ (∈-i Γ₂ x τ x₂ τ₂ x-≢-x₂ x-∈-Γ₂) rewrite concat-ident-l Γ₂ =
  ∈-i Γ₂ x τ x₂ τ₂ x-≢-x₂ x-∈-Γ₂
in-in-concat (Γ₁ , x₁ ∶ τ₁) Γ₂ x τ x-∈-Γ₂ rewrite concat-comm-ext Γ₁ Γ₂ x₁ τ₁ =
  let x-∈-Γ₂' : x ∶ τ ∈ (∅ , x₁ ∶ τ₁ , Γ₂)
      x-∈-Γ₂' = in-in-nil-ext-concat Γ₂ x τ x₁ τ₁ x-∈-Γ₂ in
  in-in-concat Γ₁ (∅ , x₁ ∶ τ₁ , Γ₂) x τ x-∈-Γ₂'

-- If the entry is `x ∶ τ` is in the extension of the context `Γ` with the entry `x' ∶ τ'`,
-- and `x` is distinct from `x'`, then `x ∶ τ` is in `Γ`.
in-ext-distinct-in : ∀ Γ x τ x' τ'
  → x ∶ τ ∈ Γ , x' ∶ τ'
  → x ≢ x'
  → x ∶ τ ∈ Γ
in-ext-distinct-in Γ x τ x τ (∈-b Γ x τ) x-≢-x = contradiction refl x-≢-x
in-ext-distinct-in Γ x τ x' τ' (∈-i Γ x τ x' τ' _ x-∈-Γ) _ = x-∈-Γ

-- If the entry `x ∶ τ` is in the concatenation of the contexts `Γ₁` and `Γ₂`,
-- and `x` is not in `Γ₂`, then `x ∶ τ` is in `Γ₁`.
in-concat-out-in : ∀ Γ₁ Γ₂ x τ
  → x ∶ τ ∈ Γ₁ , Γ₂
  → x ∉ Γ₂
  → x ∶ τ ∈ Γ₁
in-concat-out-in Γ₁ ∅ x τ x-∈-Γ (∉-b x) = x-∈-Γ
in-concat-out-in Γ₁ (Γ₂ , x₂ ∶ τ₂) x τ x-∈-Γ (∉-i Γ₂ x x₂ τ₂ x-≢-x₂ x-∉-Γ₂) =
  let x-∈-Γ' : x ∶ τ ∈ (Γ₁ , Γ₂)
      x-∈-Γ' = in-ext-distinct-in (Γ₁ , Γ₂) x τ x₂ τ₂ x-∈-Γ x-≢-x₂ in
  in-concat-out-in Γ₁ Γ₂ x τ x-∈-Γ' x-∉-Γ₂

-- Uniqueness of type under inclusion, which means that if the entries `x ∶ τ₁`
-- and `x ∶ τ₂` are in the context `Γ`, then `τ₁` is equivalent to `τ₂`.
in-unique : ∀ Γ x τ₁ τ₂
  → x ∶ τ₁ ∈ Γ
  → x ∶ τ₂ ∈ Γ
  → τ₁ ≡ τ₂
in-unique (Γ , x ∶ τ) x τ₁ τ₂ (∈-b Γ x τ₁) (∈-b Γ x τ₂) =
  refl
in-unique (Γ , x' ∶ τ') x τ₁ τ₂ (∈-i Γ x τ₁ x' τ' _ x-∈-Γ₁) (∈-i Γ x τ₂ x' τ' _ x-∈-Γ₂) =
  in-unique Γ x τ₁ τ₂ x-∈-Γ₁ x-∈-Γ₂
in-unique (Γ , x ∶ τ) x τ₁ τ₂ (∈-b Γ x τ₁) (∈-i Γ x τ₂ x' τ' x-≢-x _) =
  contradiction refl x-≢-x
in-unique (Γ , x ∶ τ) x τ₁ τ₂ (∈-i Γ x τ₁ x' τ' x-≢-x _) (∈-b Γ x τ₂) =
  contradiction refl x-≢-x
