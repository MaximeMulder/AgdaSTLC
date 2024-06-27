open import Data.Product using (_×_) renaming (_,_ to ⟨_,_⟩)
open import Data.String
open import Data.String.Properties using (_≟_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary
open import Relation.Nullary.Decidable
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; sym; ≢-sym; cong; refl)

infix 22 _⊢_∶_
infixl 21 _,_∶_
infix 20 _∶_∈_
infix 20 _∉_

data Type : Set where
  ty-bool : Type
  ty-abs  : Type → Type → Type

data Ctx : Set  where
  ∅ : Ctx
  _,_∶_ : Ctx → String → Type → Ctx

infixl 21 _,_

_,_ : Ctx → Ctx → Ctx
Γ , ∅ = Γ
Γ , (Γ' , x ∶ τ) = (Γ , Γ') , x ∶ τ

concat-ident-l : ∀ Γ → ∅ , Γ ≡ Γ
concat-ident-l ∅ = refl
concat-ident-l (Γ , x ∶ τ) = cong (λ Γ → Γ , x ∶ τ) (concat-ident-l Γ)

concat-cons-l : ∀ Γ Γ' x τ → (Γ , x ∶ τ , Γ') ≡ Γ , (∅ , x ∶ τ , Γ')
concat-cons-l Γ ∅ x τ = refl
concat-cons-l Γ (Γ' , _ ∶ _) x τ rewrite concat-cons-l Γ Γ' x τ = refl

data _∶_∈_ : String → Type → Ctx → Set where
  ∈-b : ∀ Γ x τ
    → x ∶ τ ∈ Γ , x ∶ τ
  ∈-i : ∀ Γ x τ x' τ'
    → x ≢ x'
    → x ∶ τ ∈ Γ
    → x ∶ τ ∈ Γ , x' ∶ τ'

data _∉_ : String → Ctx → Set where
  ∉-b : ∀ x
    → x ∉ ∅
  ∉-i : ∀ Γ x x' τ'
    → x ≢ x'
    → x ∉ Γ
    → x ∉ Γ , x' ∶ τ'

in-out-distinct : ∀ Γ x y τ
  → x ∶ τ ∈ Γ
  → y ∉ Γ
  → x ≢ y
in-out-distinct ∅ x y τ ()
in-out-distinct (Γ , x ∶ τ) x y τ (∈-b Γ x τ) (∉-i Γ y x τ ≢-yx _) =
  ≢-sym ≢-yx
in-out-distinct (Γ , x' ∶ τ') x y τ (∈-i Γ x τ x' τ' _ ∈-x-Γ) (∉-i Γ y x' τ' _ ∉-y-Γ) =
  in-out-distinct Γ x y τ ∈-x-Γ ∉-y-Γ

in-concat-either-in-out : ∀ Γ₁ Γ₂ x τ
  → x ∶ τ ∈ (Γ₁ , Γ₂)
  → x ∶ τ ∈ Γ₁ × x ∉ Γ₂ ⊎ x ∶ τ ∈ Γ₂
in-concat-either-in-out Γ₁ ∅ x τ x-∈-Γ₁ =
  inj₁ ⟨ x-∈-Γ₁ , ∉-b x ⟩
in-concat-either-in-out Γ₁ (Γ₂ , x₂ ∶ τ₂) x τ (∈-b Γ x τ) =
  inj₂ (∈-b Γ₂ x τ)
in-concat-either-in-out Γ₁ (Γ₂ , x₂ ∶ τ₂) x τ (∈-i Γ x τ x₂ τ₂ x-≢-x₂ x-∈-Γ) with in-concat-either-in-out Γ₁ Γ₂ x τ x-∈-Γ
... | inj₁ ⟨ x-∈-Γ₁ , x-∉-Γ₂ ⟩ = inj₁ ⟨ x-∈-Γ₁ , ∉-i Γ₂ x x₂ τ₂ x-≢-x₂ x-∉-Γ₂ ⟩
... | inj₂ x-∈-Γ₂ = inj₂ (∈-i Γ₂ x τ x₂ τ₂ x-≢-x₂ x-∈-Γ₂)

in-out-in-concat : ∀ Γ₁ Γ₂ x τ
  → x ∶ τ ∈ Γ₁
  → x ∉ Γ₂
  → x ∶ τ ∈ (Γ₁ , Γ₂)
in-out-in-concat Γ₁ ∅ x τ x-∈-Γ₁ x-∉-Γ₂ = x-∈-Γ₁
in-out-in-concat Γ₁ (Γ₂ , x₂ ∶ τ₂) x τ x-∈-Γ₁ (∉-i Γ₂ x x₂ τ₂ x-≢-x₂ x-∉-Γ₂) =
  let x-∈-Γ' : x ∶ τ ∈ (Γ₁ , Γ₂)
      x-∈-Γ' = in-out-in-concat Γ₁ Γ₂ x τ x-∈-Γ₁ x-∉-Γ₂ in
  ∈-i (Γ₁ , Γ₂) x τ x₂ τ₂ x-≢-x₂ x-∈-Γ'

in-in-nil-cons-concat : ∀ Γ x τ x' τ'
  → x ∶ τ ∈ Γ
  → x ∶ τ ∈ (∅ , x' ∶ τ' , Γ)
in-in-nil-cons-concat (Γ , x ∶ τ) x τ x' τ' (∈-b Γ x τ) = ∈-b (∅ , x' ∶ τ' , Γ) x τ
in-in-nil-cons-concat (Γ , x'' ∶ τ'') x τ x' τ' (∈-i Γ x τ x'' τ'' x-≢-x'' x-∈-Γ) =
  let x-∈-Γ' : x ∶ τ ∈ (∅ , x' ∶ τ' , Γ)
      x-∈-Γ' = in-in-nil-cons-concat Γ x τ x' τ' x-∈-Γ in
  ∈-i (∅ , x' ∶ τ' , Γ) x τ x'' τ'' x-≢-x'' x-∈-Γ'

in-in-concat : ∀ Γ₁ Γ₂ x τ
  → x ∶ τ ∈ Γ₂
  → x ∶ τ ∈ (Γ₁ , Γ₂)
in-in-concat ∅ Γ₂ x τ (∈-b Γ₂' x τ) rewrite concat-ident-l Γ₂' =
  ∈-b Γ₂' x τ
in-in-concat ∅ (Γ₂ , x₂ ∶ τ₂) x τ (∈-i Γ₂ x τ x₂ τ₂ x-≢-x₂ x-∈-Γ₂) rewrite concat-ident-l Γ₂ =
  ∈-i Γ₂ x τ x₂ τ₂ x-≢-x₂ x-∈-Γ₂
in-in-concat (Γ₁ , x₁ ∶ τ₁) Γ₂ x τ x-∈-Γ₂ rewrite concat-cons-l Γ₁ Γ₂ x₁ τ₁ =
  let x-∈-Γ₂' : x ∶ τ ∈ (∅ , x₁ ∶ τ₁ , Γ₂)
      x-∈-Γ₂' = in-in-nil-cons-concat Γ₂ x τ x₁ τ₁ x-∈-Γ₂ in
  in-in-concat Γ₁ (∅ , x₁ ∶ τ₁ , Γ₂) x τ x-∈-Γ₂'

in-cons-distinct-in : ∀ Γ x τ x' τ'
  → x ∶ τ ∈ Γ , x' ∶ τ'
  → x ≢ x'
  → x ∶ τ ∈ Γ
in-cons-distinct-in Γ x τ x τ (∈-b Γ x τ) x-≢-x = contradiction refl x-≢-x 
in-cons-distinct-in Γ x τ x' τ' (∈-i Γ x τ x' τ' _ x-∈-Γ) _ = x-∈-Γ

in-concat-out-in : ∀ Γ₁ Γ₂ x τ
  → x ∶ τ ∈ (Γ₁ , Γ₂)
  → x ∉ Γ₂
  → x ∶ τ ∈ Γ₁
in-concat-out-in Γ₁ ∅ x τ x-∈-Γ (∉-b x) = x-∈-Γ
in-concat-out-in Γ₁ (Γ₂ , x₂ ∶ τ₂) x τ x-∈-Γ (∉-i Γ₂ x x₂ τ₂ x-≢-x₂ x-∉-Γ₂) =
  let x-∈-Γ' : x ∶ τ ∈ (Γ₁ , Γ₂)
      x-∈-Γ' = in-cons-distinct-in (Γ₁ , Γ₂) x τ x₂ τ₂ x-∈-Γ x-≢-x₂ in
  in-concat-out-in Γ₁ Γ₂ x τ x-∈-Γ' x-∉-Γ₂

{-
  What I have : proof that it is in the full concat
  proof not in gamma 2
-}

{- in-strength : ∀ Γ₁ Γ₂ x τ x' τ'
  → x ∶ τ ∈ (Γ₁ , x' ∶ τ' , Γ₂)
  → x ≢ x'
  → x ∶ τ ∈ (Γ₁ , Γ₂) -}
{- in-strength Γ₁ (Γ₂ , x ∶ τ) x τ x' τ' (∈-b Γ x τ) x-≢-x' = () -}

data Exchange : Ctx → Ctx → Set where
  exchange : ∀ Γ Γ' x₁ τ₁ x₂ τ₂
    → x₁ ≢ x₂
    → Exchange (Γ , x₁ ∶ τ₁ , x₂ ∶ τ₂ , Γ') (Γ , x₂ ∶ τ₂ , x₁ ∶ τ₁ , Γ')

-- Extension of a context (or weakening of the proofs that use it).
data Extend : Ctx → Ctx → Set where
  extend-∉ : ∀ Γ₁ Γ₂ x τ
    → x ∉ Γ₁
    → Extend (Γ₁ , Γ₂) (Γ₁ , x ∶ τ , Γ₂)
  extend-∈ : ∀ Γ₁ Γ₂ x τ τ₂
    → x ∶ τ₂ ∈ Γ₂
    → Extend (Γ₁ , Γ₂) (Γ₁ , x ∶ τ , Γ₂)

{-
open import Relation.Binary.Construct.Closure.ReflexiveTransitive using (Star; ε; _▻_)

Extend* = Star Extend

extend*-nil : ∀ Γ → Extend* ∅ Γ
extend*-nil ∅ = ε
extend*-nil (Γ , x ∶ τ) =
  let a : Extend* ∅ Γ
      a = extend*-nil Γ in
  let b : Extend Γ (Γ , x ∶ τ)
      b = with ≟
      extend-∉ ∅ ∅ x τ (∉-b x) in
  _
-}

-- Extension is preserved under appending.
extend-cons : ∀ Γ Γ' x τ
  → Extend Γ Γ'
  → Extend (Γ , x ∶ τ) (Γ' , x ∶ τ)
extend-cons _ _ x τ (extend-∉ Γ₁ Γ₂ x' τ' x'-∉-Γ₁) =
  extend-∉ Γ₁ (Γ₂ , x ∶ τ) x' τ' x'-∉-Γ₁
extend-cons _ _ x τ (extend-∈ Γ₁ Γ₂ x' τ' τ₂ x'-∈-Γ₂) with x ≟ x'
... | yes x-≡-x' rewrite sym x-≡-x' = extend-∈ Γ₁ (Γ₂ , x ∶ τ) x τ' τ (∈-b Γ₂ x τ)
... | no  x-≢-x' = extend-∈ Γ₁ (Γ₂ , x ∶ τ) x' τ' τ₂ (∈-i Γ₂ x' τ₂ x τ (≢-sym x-≢-x') x'-∈-Γ₂)

-- Inclusion is preserved under extension.
in-extend : ∀ Γ Γ' x τ
  → Extend Γ Γ'
  → x ∶ τ ∈ Γ
  → x ∶ τ ∈ Γ'
in-extend Γ Γ' x τ (extend-∈ Γ₁ Γ₂ x' τ' τ₂ x'-∈-Γ₂) x-∈-Γ with in-concat-either-in-out Γ₁ Γ₂ x τ x-∈-Γ
... | inj₁ ⟨ x-∈-Γ₁ , x-∉-Γ₂ ⟩ =
  let x-≢-x' : x ≢ x'
      x-≢-x' = ≢-sym (in-out-distinct Γ₂ x' x τ₂ x'-∈-Γ₂ x-∉-Γ₂) in
  let x-∈-Γ' : x ∶ τ ∈ (Γ₁ , x' ∶ τ') 
      x-∈-Γ' = ∈-i Γ₁ x τ x' τ' x-≢-x' x-∈-Γ₁ in
  in-out-in-concat (Γ₁ , x' ∶ τ') Γ₂ x τ x-∈-Γ' x-∉-Γ₂
... | inj₂ x-∈-Γ₂ = in-in-concat (Γ₁ , x' ∶ τ') Γ₂ x τ x-∈-Γ₂
in-extend Γ Γ' x τ (extend-∉ Γ₁ Γ₂ x' τ' x'-∉-Γ₁) x-∈-Γ with in-concat-either-in-out Γ₁ Γ₂ x τ x-∈-Γ
... | inj₁ ⟨ x-∈-Γ₁ , x-∉-Γ₂ ⟩ =
  let x-≢-x' : x ≢ x'
      x-≢-x' = in-out-distinct Γ₁ x x' τ x-∈-Γ₁ x'-∉-Γ₁ in
  let x-∈-Γ' : x ∶ τ ∈ (Γ₁ , x' ∶ τ')
      x-∈-Γ' = ∈-i Γ₁ x τ x' τ' x-≢-x' x-∈-Γ₁ in
  in-out-in-concat (Γ₁ , x' ∶ τ') Γ₂ x τ x-∈-Γ' x-∉-Γ₂
... | inj₂ x-∈-Γ₂ = in-in-concat (Γ₁ , x' ∶ τ') Γ₂ x τ x-∈-Γ₂

{-p-idk : ∀ Γ₁ Γ₂ x τ
  → x ∶ τ ∈ (Γ₁ , Γ₂)
  → x ∉ Γ₂
  → x ∶ τ ∈ Γ₁
p-idk Γ₁ Γ₂ x τ ∈-x-Γ (∉-b x) =
  ∈-x-Γ
p-idk Γ₁ (Γ₂ , x' ∶ τ') x τ (∈-i _ x τ x' τ' _ ∈-x-Γ) (∉-i Γ₂ x x' τ' _ ∉-x-Γ₂) =
  p-idk Γ₁ Γ₂ x τ ∈-x-Γ ∉-x-Γ₂
p-idk Γ₁ (Γ₂ , x ∶ τ) x τ (∈-b _ x τ) p@(∉-i Γ₂ x x' τ' ≢-xx' ∉-x-Γ₂) =
  p-idk Γ₁ Γ₂ x τ _ ∉-x-Γ₂
-}

data Term : Set where
  tm-true  : Term
  tm-false : Term
  tm-var   : String →  Term
  tm-abs   : String → Type → Term → Term
  tm-app   : Term → Term → Term
  tm-if    : Term → Term → Term → Term

data _[_/_]⇛_ : Term → Term → String → Term → Set where
  subst-true : ∀ x eₓ
    → tm-true [ eₓ / x ]⇛ tm-true
  subst-false : ∀ x eₓ
    → tm-false [ eₓ / x ]⇛ tm-false
  subst-var-eq : ∀ x eₓ
    → (tm-var x) [ eₓ / x ]⇛ eₓ
  subst-var-ne : ∀ x eₓ y
    → x ≢ y
    → (tm-var y) [ eₓ / x ]⇛ (tm-var y)
  subst-if : ∀ x eₓ e₁ e₂ e₃ e₁' e₂' e₃'
    → e₁ [ eₓ / x ]⇛ e₁'
    → e₂ [ eₓ / x ]⇛ e₂'
    → e₃ [ eₓ / x ]⇛ e₃'
    → (tm-if e₁ e₂ e₃) [ eₓ / x ]⇛ (tm-if e₁' e₂' e₃')
  subst-abs-eq : ∀ x eₓ y τ e
    → x ≡ y
    → (tm-abs y τ e) [ eₓ / x ]⇛ (tm-abs y τ e)
  subst-abs-ne : ∀ x eₓ y τ e e'
    → x ≢ y
    → e [ eₓ / x ]⇛ e'
    → (tm-abs y τ e) [ eₓ / x ]⇛ (tm-abs y τ e')
  subst-app : ∀ x eₓ e₁ e₂ e₁' e₂'
    → e₁ [ eₓ / x ]⇛ e₁'
    → e₂ [ eₓ / x ]⇛ e₂'
    → (tm-app e₁ e₂) [ eₓ / x ]⇛ (tm-app e₁' e₂')

data _⊢_∶_ : Ctx → Term → Type → Set where
  t-true : ∀ Γ
    → Γ ⊢ tm-true ∶ ty-bool
  t-false : ∀ Γ
    → Γ ⊢ tm-false ∶ ty-bool
  t-var : ∀ Γ x τ
    → x ∶ τ ∈ Γ
    → Γ ⊢ tm-var x ∶ τ
  t-if : ∀ Γ τ e₁ e₂ e₃
    → Γ ⊢ e₁ ∶ ty-bool
    → Γ ⊢ e₂ ∶ τ
    → Γ ⊢ e₃ ∶ τ
    → Γ ⊢ tm-if e₁ e₂ e₃ ∶ τ
  t-abs : ∀ Γ x e τ₁ τ₂
    → (Γ , x ∶ τ₁) ⊢ e ∶ τ₂
    → Γ ⊢ tm-abs x τ₁ e ∶ ty-abs τ₁ τ₂
  t-app : ∀ Γ e₁ e₂ τ₁ τ₂
    → Γ ⊢ e₁ ∶ ty-abs τ₁ τ₂
    → Γ ⊢ e₂ ∶ τ₁
    → Γ ⊢ tm-app e₁ e₂ ∶ τ₂

data Value : Term → Set where
  v-true  : Value tm-true
  v-false : Value tm-false
  v-abs   : ∀ x τ e → Value (tm-abs x τ e)

data _↦_ : Term → Term → Set where
  s-if-true : ∀ e₁ e₂
    → tm-if tm-true e₁ e₂ ↦ e₁
  s-if-false : ∀ e₁ e₂
    → tm-if tm-false e₁ e₂ ↦ e₂
  s-if-step : ∀ e₁ e₁' e₂ e₃
    → e₁ ↦ e₁'
    → tm-if e₁ e₂ e₃ ↦ tm-if e₁' e₂ e₃
  s-app : ∀ e₁ e₂ x τ e
    {- → tm-app e₁ e₂ ↦ (e [ e₂ / x ]) -}
    → tm-app (tm-abs x τ e₁) e₂ ↦ e
  s-app-step : ∀ e₁ e₁' e₂
    → e₁ ↦ e₁'
    → tm-app e₁ e₂ ↦ tm-app e₁' e₂

data progress (e : Term) : Set where
  step : ∀ e'
    → e ↦ e'
    → progress e
  value :
    Value e
    → progress e

{- p-ty-idk : ∀ {Γ Γ' x τ e τₑ}
  → (Γ , x ∶ τ , Γ') ⊢ e ∶ τₑ
  → x ∶ τ ∈ Γ'
  → (Γ , Γ') ⊢ e ∶ τₑ
p-ty-idk (t-true a) _ = t-true -}

{- p-idk : ∀ Γ x τ Γ₁ Γ₂
  → Γ ≡ Γ₁ , Γ₂
  → x ∶ τ ∈ Γ
  → Either (x ∶ τ ∈ Γ₁) (x ∶ τ ∈ Γ₂)
p-idk Γ x τ Γ₁ Γ₂ equiv in -}

{-
  Inclusion is preserved under exchange.
-}
{- p-in-exchange : ∀ Γ Γ' x τ
  → Exchange Γ Γ'
  → x ∶ τ ∈ Γ
  → x ∶ τ ∈ Γ'
p-in-exchange Γ Γ' x τ (exchange aa bb x₁ τ₁ x₂ τ₂ ≢-x₁₂) (∈-i _ x τ x₂ τ₂ ≢-x₂ (∈-i _ x τ x₁ τ₁ ≢-x₁ ∈-x-Γₚ)) =
  ∈-i _ x τ x₁ τ₁ ≢-x₁ (∈-i _ _ _ _ _ ≢-x₂ ∈-x-Γₚ)
p-in-exchange Γ Γ' x τ (exchange aa bb x₁ τ₁ x₂ τ₂ ≢-x₁₂) (∈-i _ x τ x₂ τ₂ ≢-x₂ (∈-b _ x τ)) =
  ∈-b _ x τ
p-in-exchange Γ Γ' x τ (exchange aa bb x₁ τ₁ x₂ τ₂ ≢-x₁₂) (∈-b _ x₂ τ₂) with x ≟ x₁
... | no  ≢-x₁ = ∈-i _ x τ x₁ τ₁ ≢-x₁ (∈-b _ x τ)
... | yes ≡-x₁ = ∈-i _ x₂ τ₂ x₁ τ₁ (≢-sym ≢-x₁₂) (∈-b _ x₂ τ₂) -}

{-
  Typing is preserved under exchange.
-}
{- p-ty-exchange : ∀ Γ Γ' e τ
  → Exchange Γ Γ'
  → Γ ⊢ e ∶ τ
  → Γ' ⊢ e ∶ τ
p-ty-exchange Γ Γ' tm-true ty-bool _ (t-true Γ) = t-true Γ'
p-ty-exchange Γ Γ' tm-false ty-bool _ (t-false Γ) = t-false Γ'
p-ty-exchange Γ Γ' (tm-if e₁ e₂ e₃) τ p (t-if Γ τ e₁ e₂ e₃ te₁ te₂ te₃) =
  let te₁' : Γ' ⊢ e₁ ∶ ty-bool
      te₁' = p-ty-exchange Γ Γ' e₁ ty-bool p te₁ in
  let te₂' : Γ' ⊢ e₂ ∶ τ
      te₂' = p-ty-exchange Γ Γ' e₂ τ p te₂ in
  let te₃' : Γ' ⊢ e₃ ∶ τ
      te₃' = p-ty-exchange Γ Γ' e₃ τ p te₃ in
  t-if Γ' τ e₁ e₂ e₃ te₁' te₂' te₃'
p-ty-exchange Γ Γ' (tm-var x) τ p (t-var Γ x τ ∈-x-τ-Γ) =
  t-var Γ' x τ (p-in-exchange Γ Γ' x τ p ∈-x-τ-Γ)
p-ty-exchange Γ Γ' (tm-app e₁ e₂) τ₂ p (t-app Γ e₁ e₂ τ₁ τ₂ te₁ te₂) =
  let te₁' : Γ' ⊢ e₁ ∶ ty-abs τ₁ τ₂
      te₁' = p-ty-exchange Γ Γ' e₁ (ty-abs τ₁ τ₂) p te₁ in
  let te₂' : Γ' ⊢ e₂ ∶ τ₂
      te₂' = p-ty-exchange Γ Γ' e₂ τ₂ p te₂ in
  t-app Γ' e₁ e₂ τ₁ τ₂ te₁' te₂'
p-ty-exchange Γ Γ' (tm-abs x τ₁ e) _ p (t-abs Γ x τ₁ τ₂ e te₂) =
  t-abs Γ' x τ₁ τ₂ e _ -}

-- Typing is preserved under weakening
ty-weaken : ∀ Γ Γ' e τ
  → Extend Γ Γ'
  → Γ ⊢ e ∶ τ
  → Γ' ⊢ e ∶ τ
ty-weaken Γ Γ' _ _ _ (t-true Γ) = t-true Γ'
ty-weaken Γ Γ' _ _ _  (t-false Γ) = t-false Γ'
ty-weaken Γ Γ' _ _ w (t-var Γ x τ x-∈-Γ) =
  let x-∈-Γ' : x ∶ τ ∈ Γ'
      x-∈-Γ' = in-extend Γ Γ' x τ w x-∈-Γ in
  t-var Γ' x τ x-∈-Γ'
ty-weaken Γ Γ' _ τ w (t-if Γ τ e₁ e₂ e₃ te₁ te₂ te₃) =
  let te₁' : Γ' ⊢ e₁ ∶ ty-bool
      te₁' = ty-weaken Γ Γ' e₁ ty-bool w te₁ in
  let te₂' : Γ' ⊢ e₂ ∶ τ
      te₂' = ty-weaken Γ Γ' e₂ τ w te₂ in
  let te₃' : Γ' ⊢ e₃ ∶ τ
      te₃' = ty-weaken Γ Γ' e₃ τ w te₃ in
  t-if Γ' τ e₁ e₂ e₃ te₁' te₂' te₃'
ty-weaken Γ Γ' _ _ w (t-abs Γ x e₂ τ₁ τ₂ te₂) =
  let w' : Extend (Γ , x ∶ τ₁) (Γ' , x ∶ τ₁)
      w' = extend-cons Γ Γ' x τ₁ w in
  let te₂' : (Γ' , x ∶ τ₁) ⊢ e₂ ∶ τ₂ 
      te₂' = ty-weaken (Γ , x ∶ τ₁) (Γ' , x ∶ τ₁) e₂ τ₂ w' te₂ in
  t-abs Γ' x e₂ τ₁ τ₂ te₂'
ty-weaken Γ Γ' _ τ w (t-app Γ e₁ e₂ τ₁ τ te₁ te₂) =
  let te₁' : Γ' ⊢ e₁ ∶ ty-abs τ₁ τ 
      te₁' = ty-weaken Γ Γ' e₁ (ty-abs τ₁ τ) w te₁ in
  let te₂' : Γ' ⊢ e₂ ∶ τ₁
      te₂' = ty-weaken Γ Γ' e₂ τ₁ w te₂ in
  t-app Γ' e₁ e₂ τ₁ τ te₁' te₂'

{- ty-weaken-nil : ∀ Γ e τ
  → ∅ ⊢ e ∶ τ
  → Γ ⊢ e ∶ τ -}
  
-- Typing is preserved under substitution.
ty-subst : ∀ Γ x eₓ τₓ e τ e'
  → ∅ ⊢ eₓ ∶ τₓ
  → (Γ , x ∶ τₓ) ⊢ e ∶ τ
  → e [ eₓ / x ]⇛ e'
  → Γ ⊢ e' ∶ τ
ty-subst Γ x eₓ τₓ e τ e' _ (t-true (Γ , x ∶ τₓ)) (subst-true x eₓ) =
  t-true Γ
ty-subst Γ x eₓ τₓ e τ e' _ (t-false (Γ , x ∶ τₓ)) (subst-false x eₓ) =
  t-false Γ
{- p-ty-subst x eₓ τₓ e τ e' teₓ (t-var (Γ , x ∶ τₓ) y τ (∈-b x τₓ ∅)) (subst-var-ne x eₓ y) = _ {- t-var (x ↪ τₓ :: ∅) x τₓ (∈-b x τₓ ∅) -} -}
{- p-ty-subst Γ x eₓ τₓ e τ e' teₓ {- (t-var (_ , x ∶ τₓ) x τ (∈-b x τₓ _))-} _ (subst-var-eq x eₓ) = _ -}
{- ty-subst Γ x eₓ τ e τ e' teₓ (t-var (Γ , x ∶ τ) x τ x-∈-Γ) (subst-var-eq x eₓ) = ty-weaken-nil Γ eₓ τ teₓ -}
ty-subst Γ x eₓ τₓ e τ e' teₓ (t-var (Γ , x ∶ τₓ) x' τ x'-∈-Γ) (subst-var-ne x eₓ x' x-≢-x') =
  let x'-∈-Γ : x' ∶ τ ∈ Γ
      x'-∈-Γ = in-cons-distinct-in Γ x' τ x τₓ x'-∈-Γ (≢-sym x-≢-x') in
  t-var Γ x' τ x'-∈-Γ
ty-subst Γ x eₓ τₓ e τ e' teₓ (t-if (Γ , x ∶ τₓ) τ e₁ e₂ e₃ te₁ te₂ te₃) (subst-if x eₓ e₁ e₂ e₃ e₁' e₂' e₃' se₁' se₂' se₃') =
  let te₁' : Γ  ⊢ e₁' ∶ ty-bool
      te₁' = ty-subst Γ x eₓ τₓ e₁ ty-bool e₁' teₓ te₁ se₁' in
  let te₂' : Γ  ⊢ e₂' ∶ τ
      te₂' = ty-subst Γ x eₓ τₓ e₂ τ e₂' teₓ te₂ se₂' in
  let te₃' : Γ  ⊢ e₃' ∶ τ
      te₃' = ty-subst Γ x eₓ τₓ e₃ τ e₃' teₓ te₃ se₃' in
  t-if Γ τ e₁' e₂' e₃' te₁' te₂' te₃'
{- p-ty-subst Γ x eₓ τₓ e τ e' teₓ (t-abs (x ↪ τₓ :: Γ) y τ₁ τ₂ e₂ te₂) (subst-abs x eₓ y τ₁ e₂ e₂' se₂') =
  {- te₂ : (y ↪ τ₁ :: (x ↪ τₓ :: Γ)) ⊢ e₂ ∶ τ₂
     ?0 : (x ↪ τₓ :: (y ↪ τ₁ :: Γ)) ⊢ e₂ ∶ τ₂
  let i : (y ↪ τ₁ :: Γ) ⊢ e₂' ∶ τ₂
      i = p-ty-subst (y ↪ τ₁ :: Γ) x eₓ τₓ e₂ τ₂ e₂' teₓ {!  !} se₂' in -}
  t-abs Γ y τ₁ τ₂ e₂' _ -}
{- p-ty-subst Γ x eₓ τₓ e τ e' teₓ (t-abs (Γ , x ∶ τₓ) x₁ τ₁ τ₂ e₂ te₂) (subst-abs-eq x eₓ x₁ τ₁ e₂ x-≡-x₁) =
  let e₂-∶-τ₂ : 
      e₂-∶-τ₂ = _ in
      
  t-abs Γ x τ₁ τ₂ e₂ _ -}
ty-subst Γ x eₓ τₓ e τ e' teₓ (t-app (Γ , x ∶ τₓ) e₁ e₂ τ₁ τ₂ te₁ te₂) (subst-app x eₓ e₁ e₂ e₁' e₂' se₁ se₂) =
  let te₁' : Γ ⊢ e₁' ∶ ty-abs τ₁ τ₂
      te₁' = ty-subst Γ x eₓ τₓ e₁ (ty-abs τ₁ τ₂) e₁' teₓ te₁ se₁ in
  let te₂' : Γ ⊢ e₂' ∶ τ₁
      te₂' = ty-subst Γ x eₓ τₓ e₂ τ₁ e₂' teₓ te₂ se₂ in
  t-app Γ e₁' e₂' τ₁ τ₂ te₁' te₂'


{-
  Γ, x ∶ τₓ ⊢ λy. e : τ   ∅ ⊢ eₓ ∶ τₓ   x ≡ y   (λy. e)[eₓ/x] ⇛ (λy. e)
-}


{- p-ty-subst Γ x τₓ eₓ e τ  e' (t-abs (x ↪ τₓ :: Γ) y τ₁ τ₂ e'' te'') _ _ = _ -}

{-
p-progress : ∀ e τ → (∅ ⊢ e ∶ τ) → progress e
p-progress e τ (t-true ∅) = value v-true
p-progress e τ (t-false ∅) = value v-false
p-progress e τ (t-if ∅ τ e₁ e₂ e₃ te₁ _ _) with p-progress e₁ ty-bool te₁
... | value v-true = step e₂ (s-if-true e₂ e₃)
... | value v-false = step e₃ (s-if-false e₂ e₃)
... | step e₁' pe₁ = step (tm-if e₁' e₂ e₃) (s-if-step e₁ e₁' e₂ e₃ pe₁)
p-progress e τ (t-abs ∅ x τ₁ τ₂ e' _) = value (v-abs x τ₁ e')
p-progress e τ (t-var ∅ x τ ())
p-progress e τ (t-app ∅ e₁ e₂ τ₁ τ₂ te₁ _) with p-progress e₁ (ty-abs τ₁ τ₂) te₁
... | step e₁' pe₁ = step (tm-app e₁' e₂) (s-app-step e₁ e₁' e₂ pe₁) -}
{- ... | value (v-abs x τ₁ e') = step (tm) () -}
