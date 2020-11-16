-- Length-indexed lists as a recursive family
-- From "Dependent Types at Work", section 3.1

module RecVec where

open import Data.Nat
open import Data.Empty
open import Data.Unit
open import Data.Maybe hiding (map ; zip)
open import Data.Product hiding (map ; zip)

private
  variable
    m n : ℕ
    A B : Set

Vec : Set → ℕ → Set
Vec A zero = ⊤
Vec A (suc n) = A × Vec A n

head : Vec A (suc n) → A
head (a , _) = a

tail : Vec A (suc n) → Vec A n
tail (_ , as) = as

map : (A → B) → Vec A n → Vec B n
map {n = zero } _ tt = tt
map {n = suc _} f (a , as) = f a , map f as

zip : Vec A n → Vec B n → Vec (A × B) n
zip {n = zero } tt tt = tt
zip {n = suc _} (a , as) (b , bs) = (a , b) , zip as bs


Fin : ℕ → Set
Fin zero = ⊥
Fin (suc n) = Maybe (Fin n)

_!_ : Vec A n → Fin n → A
_!_ {n = suc m} (a , _ ) nothing = a
_!_ {n = suc m} (_ , as) (just i) = as ! i

