{-# OPTIONS --rewriting #-}

module Misc where

open import Level renaming (suc to lsuc)
open import Data.Nat
open import Data.Nat.Properties using (+-assoc)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning
open import Data.Vec
-- open import Relation.Binary.HeterogeneousEquality as H using (_≅_; refl)

{-# BUILTIN REWRITE _≡_ #-}

private
  variable
    ℓ ℓ′ : Level
    n m o : ℕ
    A : Set ℓ
    B : Set ℓ′

n+1 : n + 1 ≡ suc n
n+1 {zero} = refl
n+1 {suc n} = cong suc (n+1 {n})
{-# REWRITE n+1 #-}

n+0 : n + 0 ≡ n
n+0 {zero} = refl
n+0 {suc n} = cong suc (n+0 {n})
{-# REWRITE n+0 #-}

map-++ : (f : A → B) → (as₁ : Vec A n) → (as₂ : Vec A m)
       → map f as₁ ++ map f as₂ ≡ map f (as₁ ++ as₂)
map-++ f [] as₂ = refl
map-++ f (x ∷ as₁) as₂ = cong (f x ∷_) (map-++ f as₁ as₂)
-- {-# REWRITE map-++ #-}

-- Needs heterogeneous equality
-- Already in Data.Vec.Properties.WithK
-- ++-assoc : (as₁ : Vec A n) → (as₂ : Vec A m) → (as₃ : Vec A o)
--          → (as₁ ++ as₂) ++ as₃ ≡ as₁ ++ (as₂ ++ as₃)
-- ++-assoc as₁ as₂ as₃ = ?

{-

-- Triggers an Agda "Internal Error" when used.

module _ where

  private
    -- Trick to work avoid need for heterogeneous equality
    +-assoc′ : ∀ (m n o : ℕ) → (m + n) + o ≡ m + (n + o)
    +-assoc′ = +-assoc
    {-# REWRITE +-assoc′ #-}

  ++-assoc : ∀ (as₁ : Vec A m) (as₂ : Vec A n) (as₃ : Vec A o)
           → (as₁ ++ as₂) ++ as₃ ≡ as₁ ++ (as₂ ++ as₃)
  ++-assoc [] as₂ as₃ = refl
  ++-assoc (x ∷ as₁) as₂ as₃
    rewrite (++-assoc as₁ as₂ as₃) = refl

-}
