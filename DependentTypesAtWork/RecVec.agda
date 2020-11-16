-- Length-indexed lists as a recursive family
-- From "Dependent Types at Work", section 3.1

module RecVec where

open import Level renaming (suc to lsuc)
open import Data.Nat hiding (_^_)
open import Data.Empty.Polymorphic
open import Data.Unit.Polymorphic
open import Data.Maybe hiding (map ; zip)
open import Data.Product hiding (map ; zip)

private
  variable
    m n : ℕ
    ℓ ℓ′ : Level
    A : Set ℓ
    B : Set ℓ′

-- Vec : Set ℓ → ℕ → Set ℓ
-- Vec A zero = ⊤
-- Vec A (suc n) = A × Vec A n

-- Generalize Vec

open import Function

_^_ : (A → A) → ℕ → (A → A)
f ^ zero  = id
f ^ suc n = f ∘ (f ^ n)

Vec : Set ℓ → ℕ → Set ℓ
Vec A n = ((A ×_) ^ n) ⊤

head : Vec A (suc n) → A
head (a , _) = a

tail : Vec A (suc n) → Vec A n
tail (_ , as) = as

map : (A → B) → Vec A n → Vec B n
map {n = zero } _ _ = tt
map {n = suc n} f (a , as) = f a , map {n = n} f as

zip : Vec A n → Vec B n → Vec (A × B) n
zip {n = zero } _ _ = tt
zip {n = suc n} (a , as) (b , bs) = (a , b) , zip {n = n} as bs

Fin : ℕ → Set
Fin zero = ⊥
Fin (suc n) = Maybe (Fin n)

_!_ : Vec A n → Fin n → A
_!_ {n = suc m} (a , _ ) nothing = a
_!_ {n = suc m} (_ , as) (just i) = as ! i

-- Perfect binary leaf tree
BTree : Set ℓ → ℕ → Set ℓ
BTree A n = ((λ τ → τ × τ) ^ n) A

-- More convenient to define. Perhaps better fits Haskell style.
BTree′ : ℕ → Set ℓ → Set ℓ
BTree′ = (λ τ → τ × τ) ^_
