-- From "Dependent Types at Work", section 3.3 

module BalancedTree where

open import Level using (Level)
open import Data.Nat

private
  variable
    ℓ : Level

-- Perfect binary leaf trees
data Perfect (A : Set ℓ) : ℕ → Set ℓ where
  plf : A → Perfect A zero
  pnd : {n : ℕ} → Perfect A n → Perfect A n → Perfect A (suc n)

-- Exercise: Modify the above definition in order to define the height balanced
-- binary trees, that is, binary trees where the difference between the heights
-- of the left and right subtree is at most one.

-- Two numbers differing by at most one, along with their maximum
data WithinOne : ℕ → ℕ → ℕ → Set where
  n,n   : ∀ (n : ℕ) → WithinOne n n n
  n,n+1 : ∀ (n : ℕ) → WithinOne n (suc n) (suc n)
  n+1,n : ∀ (n : ℕ) → WithinOne (suc n) n (suc n)

-- Height-balanced binary leaf trees
data Balanced (A : Set ℓ) : ℕ → Set ℓ where
  blf : A → Balanced A zero
  bnd : {m n p : ℕ} → Balanced A m → Balanced A n → WithinOne m n p → Balanced A (suc p)

-- I could instead omit the max from WithinOne and define a max function on that
-- type instead.
