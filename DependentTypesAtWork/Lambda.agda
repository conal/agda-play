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
  ⊤ : Ty
  _⟶_ : Ty → Ty → Ty

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
  Var′ : (Γ : Context n) → (i : Fin n) → L′ Γ (lookup Γ i)
  App′ : L′ Γ (σ ⟶ τ) → L′ Γ σ → L′ Γ τ
  Lam′ : L′ (σ ∷ Γ) τ → L′ Γ (σ ⟶ τ)
