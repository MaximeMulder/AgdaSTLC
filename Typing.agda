open import Relation.Binary.PropositionalEquality using (sym; ≢-sym)

open import Ctx
open import CtxContract
open import CtxWeaken
open import Subst
open import Syntax

-- The typing relation, which describes a well-typed term and its type.
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

-- Preservation of typing under weakening, which means that if the context `Γ'` is
-- a weakening of the context `Γ`, and that the term `e` has type `τ` under `Γ`,
-- then `e` also has type `τ` under `Γ'`.
weaken-preserve-ty : ∀ Γ Γ' e τ
  → Weaken Γ Γ'
  → Γ ⊢ e ∶ τ
  → Γ' ⊢ e ∶ τ
weaken-preserve-ty Γ Γ' _ _ _ (t-true Γ) = t-true Γ'
weaken-preserve-ty Γ Γ' _ _ _  (t-false Γ) = t-false Γ'
weaken-preserve-ty Γ Γ' _ _ w (t-var Γ x τ x-∈-Γ) =
  let x-∈-Γ' : x ∶ τ ∈ Γ'
      x-∈-Γ' = weaken-preserve-in Γ Γ' x τ w x-∈-Γ in
  t-var Γ' x τ x-∈-Γ'
weaken-preserve-ty Γ Γ' _ τ w (t-if Γ τ e₁ e₂ e₃ te₁ te₂ te₃) =
  let te₁' : Γ' ⊢ e₁ ∶ ty-bool
      te₁' = weaken-preserve-ty Γ Γ' e₁ ty-bool w te₁ in
  let te₂' : Γ' ⊢ e₂ ∶ τ
      te₂' = weaken-preserve-ty Γ Γ' e₂ τ w te₂ in
  let te₃' : Γ' ⊢ e₃ ∶ τ
      te₃' = weaken-preserve-ty Γ Γ' e₃ τ w te₃ in
  t-if Γ' τ e₁ e₂ e₃ te₁' te₂' te₃'
weaken-preserve-ty Γ Γ' _ _ w (t-abs Γ x e₂ τ₁ τ₂ te₂) =
  let w' : Weaken (Γ , x ∶ τ₁) (Γ' , x ∶ τ₁)
      w' = weaken-mono-ext Γ Γ' x τ₁ w in
  let te₂' : (Γ' , x ∶ τ₁) ⊢ e₂ ∶ τ₂
      te₂' = weaken-preserve-ty (Γ , x ∶ τ₁) (Γ' , x ∶ τ₁) e₂ τ₂ w' te₂ in
  t-abs Γ' x e₂ τ₁ τ₂ te₂'
weaken-preserve-ty Γ Γ' _ τ w (t-app Γ e₁ e₂ τ₁ τ te₁ te₂) =
  let te₁' : Γ' ⊢ e₁ ∶ ty-abs τ₁ τ
      te₁' = weaken-preserve-ty Γ Γ' e₁ (ty-abs τ₁ τ) w te₁ in
  let te₂' : Γ' ⊢ e₂ ∶ τ₁
      te₂' = weaken-preserve-ty Γ Γ' e₂ τ₁ w te₂ in
  t-app Γ' e₁ e₂ τ₁ τ te₁' te₂'

-- Preservation of typing under reflexive-transitive weakening.
weaken*-preserve-ty : ∀ Γ Γ' e τ
  → Weaken* Γ Γ'
  → Γ ⊢ e ∶ τ
  → Γ' ⊢ e ∶ τ
weaken*-preserve-ty Γ Γ e τ (weaken*-refl Γ) te =
  te
weaken*-preserve-ty Γ Γ' e τ (weaken*-base Γ Γ' e-Γ-Γ') te =
  weaken-preserve-ty Γ Γ' e τ e-Γ-Γ' te
weaken*-preserve-ty Γ Γ'' e τ (weaken*-trans Γ Γ' Γ'' ext-Γ-Γ' ext-Γ'-Γ'') te =
  let te' : Γ' ⊢ e ∶ τ
      te' = weaken*-preserve-ty Γ Γ' e τ ext-Γ-Γ' te in
  weaken*-preserve-ty Γ' Γ'' e τ ext-Γ'-Γ'' te'

-- Preservation of typing under contraction, which means that if the context `Γ'` is
-- a contraction of the context `Γ`, and that the term `e` has type `τ` under `Γ`,
-- then `e` also has type `τ` under `Γ'`.
contract-preserve-ty : ∀ Γ Γ' e τ
  → Contract Γ Γ'
  → Γ ⊢ e ∶ τ
  → Γ' ⊢ e ∶ τ
contract-preserve-ty Γ Γ' _ _ _ (t-true Γ) = t-true Γ'
contract-preserve-ty Γ Γ' _ _ _  (t-false Γ) = t-false Γ'
contract-preserve-ty Γ Γ' _ _ c (t-var Γ x τ x-∈-Γ) =
  let x-∈-Γ' : x ∶ τ ∈ Γ'
      x-∈-Γ' = contract-preserve-in Γ Γ' x τ c x-∈-Γ in
  t-var Γ' x τ x-∈-Γ'
contract-preserve-ty Γ Γ' _ τ c (t-if Γ τ e₁ e₂ e₃ te₁ te₂ te₃) =
  let te₁' : Γ' ⊢ e₁ ∶ ty-bool
      te₁' = contract-preserve-ty Γ Γ' e₁ ty-bool c te₁ in
  let te₂' : Γ' ⊢ e₂ ∶ τ
      te₂' = contract-preserve-ty Γ Γ' e₂ τ c te₂ in
  let te₃' : Γ' ⊢ e₃ ∶ τ
      te₃' = contract-preserve-ty Γ Γ' e₃ τ c te₃ in
  t-if Γ' τ e₁ e₂ e₃ te₁' te₂' te₃'
{- contract-preserve-ty Γ Γ' _ _ w (t-abs Γ x e₂ τ₁ τ₂ te₂) =
  let w' : Contract (Γ , x ∶ τ₁) (Γ' , x ∶ τ₁)
      w' = weaken-mono-ext Γ Γ' x τ₁ w in
  let te₂' : (Γ' , x ∶ τ₁) ⊢ e₂ ∶ τ₂
      te₂' = ty-weaken (Γ , x ∶ τ₁) (Γ' , x ∶ τ₁) e₂ τ₂ w' te₂ in
  t-abs Γ' x e₂ τ₁ τ₂ te₂' -}
contract-preserve-ty Γ Γ' _ τ c (t-app Γ e₁ e₂ τ₁ τ te₁ te₂) =
  let te₁' : Γ' ⊢ e₁ ∶ ty-abs τ₁ τ
      te₁' = contract-preserve-ty Γ Γ' e₁ (ty-abs τ₁ τ) c te₁ in
  let te₂' : Γ' ⊢ e₂ ∶ τ₁
      te₂' = contract-preserve-ty Γ Γ' e₂ τ₁ c te₂ in
  t-app Γ' e₁ e₂ τ₁ τ te₁' te₂'

-- If a term `e` has type `τ` in the empty context `∅`, then `e` also has type `τ`
-- in any context.
ty-nil : ∀ Γ e τ
  → ∅ ⊢ e ∶ τ
  → Γ ⊢ e ∶ τ
ty-nil Γ e τ te =
  weaken*-preserve-ty ∅ Γ e τ (weaken*-nil Γ) te

-- Preservation of typing under substitution, which means that if a term `e`
-- has type `τ` under a context `Γ` where the entry `x ∶ τₓ` is in this
-- context, then `e` also has type `τ` under `Γ` without `x`.
-- TODO: This definition needs to be generalized to match the above comment.
-- "`Γ` without `x`" is also not properly defined. Maybe I should define a
-- deletion operation ?
subst-preserve-ty : ∀ Γ x eₓ τₓ e τ e'
  → ∅ ⊢ eₓ ∶ τₓ
  → (Γ , x ∶ τₓ) ⊢ e ∶ τ
  → e [ eₓ / x ]⇛ e'
  → Γ ⊢ e' ∶ τ
subst-preserve-ty Γ x eₓ τₓ e τ e' _ (t-true (Γ , x ∶ τₓ)) (subst-true x eₓ) =
  t-true Γ
subst-preserve-ty Γ x eₓ τₓ e τ e' _ (t-false (Γ , x ∶ τₓ)) (subst-false x eₓ) =
  t-false Γ
subst-preserve-ty Γ x eₓ τₓ e τ e' teₓ (t-var (Γ , x ∶ τₓ) x τ x-∈-Γ) (subst-var-eq x eₓ) rewrite sym (in-unique (Γ , x ∶ τₓ) x τ τₓ x-∈-Γ (∈-b Γ x τₓ)) =
  ty-nil Γ eₓ τ teₓ
subst-preserve-ty Γ x eₓ τₓ e τ e' teₓ (t-var (Γ , x ∶ τₓ) x' τ x'-∈-Γ) (subst-var-ne x eₓ x' x-≢-x') =
  let x'-∈-Γ : x' ∶ τ ∈ Γ
      x'-∈-Γ = in-ext-distinct-in Γ x' τ x τₓ x'-∈-Γ (≢-sym x-≢-x') in
  t-var Γ x' τ x'-∈-Γ
subst-preserve-ty Γ x eₓ τₓ e τ e' teₓ (t-if (Γ , x ∶ τₓ) τ e₁ e₂ e₃ te₁ te₂ te₃) (subst-if x eₓ e₁ e₂ e₃ e₁' e₂' e₃' se₁' se₂' se₃') =
  let te₁' : Γ  ⊢ e₁' ∶ ty-bool
      te₁' = subst-preserve-ty Γ x eₓ τₓ e₁ ty-bool e₁' teₓ te₁ se₁' in
  let te₂' : Γ  ⊢ e₂' ∶ τ
      te₂' = subst-preserve-ty Γ x eₓ τₓ e₂ τ e₂' teₓ te₂ se₂' in
  let te₃' : Γ  ⊢ e₃' ∶ τ
      te₃' = subst-preserve-ty Γ x eₓ τₓ e₃ τ e₃' teₓ te₃ se₃' in
  t-if Γ τ e₁' e₂' e₃' te₁' te₂' te₃'
subst-preserve-ty Γ x eₓ τₓ e τ e' teₓ (t-abs (Γ , x ∶ τₓ) x e₂ τ₁ τ₂ te₂) (subst-abs-eq x eₓ τ₁ e₂) =
  let con-Γ : Contract (Γ , x ∶ τₓ , x ∶ τ₁) (Γ , x ∶ τ₁)
      con-Γ = contract Γ (∅ , x ∶ τ₁) x τₓ τ₁ (∈-b ∅ x τ₁) in
  t-abs Γ x e₂ τ₁ τ₂ (contract-preserve-ty (Γ , x ∶ τₓ , x ∶ τ₁) (Γ , x ∶ τ₁) e₂ τ₂ con-Γ te₂)
subst-preserve-ty Γ x eₓ τₓ e τ e' teₓ (t-abs (Γ , x ∶ τₓ) x' e₂ τ₁ τ₂ te₂) (subst-abs-ne x eₓ x₁ τ₁ e₂ e₂' x-≢-x₁ se₂) =
  t-abs Γ x' e₂' τ₁ τ₂ _

{- p-subst-preserve-ty Γ x eₓ τₓ e τ e' teₓ (t-abs (x ↪ τₓ :: Γ) y τ₁ τ₂ e₂ te₂) (subst-abs x eₓ y τ₁ e₂ e₂' se₂') =
  {- te₂ : (y ↪ τ₁ :: (x ↪ τₓ :: Γ)) ⊢ e₂ ∶ τ₂
     ?0 : (x ↪ τₓ :: (y ↪ τ₁ :: Γ)) ⊢ e₂ ∶ τ₂
  let i : (y ↪ τ₁ :: Γ) ⊢ e₂' ∶ τ₂
      i = p-subst-preserve-ty (y ↪ τ₁ :: Γ) x eₓ τₓ e₂ τ₂ e₂' teₓ {!  !} se₂' in -}
  t-abs Γ y τ₁ τ₂ e₂' _ -}
{- p-subst-preserve-ty Γ x eₓ τₓ e τ e' teₓ (t-abs (Γ , x ∶ τₓ) x₁ τ₁ τ₂ e₂ te₂) (subst-abs-eq x eₓ x₁ τ₁ e₂ x-≡-x₁) =
  let e₂-∶-τ₂ :
      e₂-∶-τ₂ = _ in

  t-abs Γ x τ₁ τ₂ e₂ _ -}
subst-preserve-ty Γ x eₓ τₓ e τ e' teₓ (t-app (Γ , x ∶ τₓ) e₁ e₂ τ₁ τ₂ te₁ te₂) (subst-app x eₓ e₁ e₂ e₁' e₂' se₁ se₂) =
  let te₁' : Γ ⊢ e₁' ∶ ty-abs τ₁ τ₂
      te₁' = subst-preserve-ty Γ x eₓ τₓ e₁ (ty-abs τ₁ τ₂) e₁' teₓ te₁ se₁ in
  let te₂' : Γ ⊢ e₂' ∶ τ₁
      te₂' = subst-preserve-ty Γ x eₓ τₓ e₂ τ₁ e₂' teₓ te₂ se₂ in
  t-app Γ e₁' e₂' τ₁ τ₂ te₁' te₂'
