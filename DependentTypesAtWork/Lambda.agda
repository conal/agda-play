-- From "Dependent Types at Work", section 3.3 

-- Exercise: Define lambda terms as an inductive family indexed by the maximal
-- number of free variables allowed in the term.

open import Data.Nat
open import Data.Fin

private
  variable
    n : ℕ

data L : ℕ → Set where
  Var : Fin n → L n
  App : L n → L n → L n
  Lam : L (suc n) → L n

-- Try also to define typed lambda terms as an inductive family indexed by the
-- type of the term.

data Ty : Set where
  unit : Ty
  _⟶_ : Ty → Ty → Ty

open import Data.Unit

evalTy : Ty → Set
evalTy unit = ⊤
evalTy (σ ⟶ τ) = evalTy σ → evalTy τ

open import Data.Vec

Context : ℕ → Set
Context n = Vec Ty n

private
  variable
    σ τ : Ty
    Γ : Context n

-- data L′ : Context n → Ty → Set where
--   Var′ : (Γ : Context n) → (i : Fin n) → Γ [ i ]= τ → L′ Γ τ
--   App′ : L′ Γ (σ ⟶ τ) → L′ Γ σ → L′ Γ τ
--   Lam′ : L′ (σ ∷ Γ) τ → L′ Γ (σ ⟶ τ)

-- Fine, but try an alternative:

data L′ : Context n → Ty → Set where
  Var′ : {Γ : Context n} → (i : Fin n) → L′ Γ (lookup Γ i)
  App′ : L′ Γ (σ ⟶ τ) → L′ Γ σ → L′ Γ τ
  Lam′ : L′ (σ ∷ Γ) τ → L′ Γ (σ ⟶ τ)

data Env : Context n → Set where
  nil : Env []
  cons : {τ : Ty} → evalTy τ → Env Γ → Env (τ ∷ Γ)

lookupEnv : {Γ : Context n} → (ρ : Env Γ) → (i : Fin n) → evalTy (lookup Γ i)
lookupEnv {Γ = τ ∷ _} (cons x _) zero = x
lookupEnv {Γ = _ ∷ Γ} (cons _ ρ) (suc i) = lookupEnv ρ i

evalL′ : L′ Γ τ → Env Γ → evalTy τ
evalL′ (Var′ i)   ρ = lookupEnv ρ i
evalL′ (App′ u v) ρ = (evalL′ u ρ) (evalL′ v ρ)
evalL′ (Lam′ u)   ρ = λ x → evalL′ u (cons x ρ)

evalL′₀ : L′ [] τ → evalTy τ
evalL′₀ e = evalL′ e nil
