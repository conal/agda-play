-- From "Dependent Types at Work", section 3.3 

-- Exercise: Define lambda terms as an inductive family indexed by the maximal
-- number of free variables allowed in the term.

open import Data.Nat
open import Data.Fin

private
  variable
    n : ℕ

data L₁ : ℕ → Set where
  Var₁ : Fin n → L₁ n
  App₁ : L₁ n → L₁ n → L₁ n
  Lam₁ : L₁ (suc n) → L₁ n

-- Try also to define typed lambda terms as an inductive family indexed by the
-- type of the term.

data Ty : Set where
  unit : Ty
  _⟶_ : Ty → Ty → Ty

open import Data.Unit

⟦_⟧ₜ : Ty → Set
⟦ unit ⟧ₜ = ⊤
⟦ σ ⟶ τ ⟧ₜ = ⟦ σ ⟧ₜ → ⟦ τ ⟧ₜ

open import Data.Vec

Context : ℕ → Set
Context n = Vec Ty n

private
  variable
    σ τ : Ty
    Γ : Context n

data L : Context n → Ty → Set where
  Var : {Γ : Context n} → (i : Fin n) → L Γ (lookup Γ i)
  App : L Γ (σ ⟶ τ) → L Γ σ → L Γ τ
  Lam : L (σ ∷ Γ) τ → L Γ (σ ⟶ τ)

data Env : Context n → Set where
  [] : Env []
  _∷_ : {τ : Ty} → ⟦ τ ⟧ₜ → Env Γ → Env (τ ∷ Γ)

lookupEnv : {Γ : Context n} → (ρ : Env Γ) → (i : Fin n) → ⟦ lookup Γ i ⟧ₜ
lookupEnv {Γ = τ ∷ _} (x ∷ _) zero = x
lookupEnv {Γ = _ ∷ Γ} (_ ∷ ρ) (suc i) = lookupEnv ρ i

⟦_⟧ : L Γ τ → Env Γ → ⟦ τ ⟧ₜ
⟦ Var i ⟧   ρ = lookupEnv ρ i
⟦ App u v ⟧ ρ = (⟦ u ⟧ ρ) (⟦ v ⟧ ρ)
⟦ Lam u ⟧   ρ = λ x → ⟦ u ⟧ (x ∷ ρ)

⟦_⟧₀ : L [] τ → ⟦ τ ⟧ₜ
⟦ e ⟧₀ = ⟦ e ⟧ []

-- TODO: rework evalL to avoid evalL under λ .
