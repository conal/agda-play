{-# OPTIONS --rewriting #-}

-- Perfect binary leaf tree

module Perfect where

open import Level using (Level)
open import Function using (_∘_)
open import Data.Nat
open import Data.Nat.Properties using (+-assoc)
open import Data.Vec
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym ; cong)
open Eq.≡-Reasoning

open import Misc

private
  variable
    ℓ : Level
    n m : ℕ
    A : Set ℓ

-- Perfect binary leaf trees
data Perfect (A : Set ℓ) : ℕ → Set ℓ where
  lf : A → Perfect A zero
  nd : Perfect A n → Perfect A n → Perfect A (suc n)

-- Naïve, expensive version
flatten : Perfect A n → Vec A (2 ^ n)
flatten (lf x) = [ x ]
flatten (nd u v) = flatten u ++ flatten v

lem : ∀ {n m} → 2 ^ n + (2 ^ n + m) ≡ 2 ^ suc n + m
lem {n} {m} = sym (+-assoc (2 ^ n) (2 ^ n) m)
{-# REWRITE lem #-}

-- lem {zero} = refl
-- lem {suc n} = {!!}

-- Optimized version, linear in time and space.
flat : Perfect A n → Vec A m → Vec A (2 ^ n + m)
flat (lf x)   = x ∷_
flat (nd u v) = flat u ∘ flat v

flatten′ : Perfect A n → Vec A (2 ^ n)
flatten′ t = flat t []
