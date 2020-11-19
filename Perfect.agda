{-# OPTIONS --rewriting #-}

-- Perfect binary leaf tree

module Perfect where

open import Level using (Level)
open import Function using (_∘_)
open import Data.Nat
open import Data.Nat.Properties using (+-assoc)
open import Data.Vec as Vec hiding (map)
import Relation.Binary.PropositionalEquality as Eq

-- open Eq using (_≡_; refl; sym ; cong ; cong₂)
open Eq using (_≡_) renaming (refl to refl≡)
-- open Eq.≡-Reasoning

open import Misc

private
  variable
    ℓ ℓ′ : Level
    m n o : ℕ
    A : Set ℓ
    B : Set ℓ′

-- Perfect binary leaf trees
data T (A : Set ℓ) : ℕ → Set ℓ where
  lf : A → T A zero
  nd : T A n → T A n → T A (suc n)

-- Naïve, expensive version
flatten : T A n → Vec A (2 ^ n)
flatten (lf x) = [ x ]
flatten (nd u v) = flatten u ++ flatten v

{-

private
  sym-+-assoc : ∀ {m n o} → m + (n + o) ≡ (m + n) + o
  sym-+-assoc {m} {n} {o} = sym (+-assoc m n o)
  -- {-# REWRITE sym-+-assoc #-}

-- Optimized version, linear in time and space.
flat : T A n → Vec A m → Vec A (2 ^ n + m)
flat (lf x)   = x ∷_
flat (nd u v) = flat u ∘ flat v where {-# REWRITE sym-+-assoc #-}

flatten′ : T A n → Vec A (2 ^ n)
flatten′ t = flat t []

module _ where

  private
    -- Trick to work avoid need for heterogeneous equality
    +-assoc′ : ∀ {m n o} → (m + n) + o ≡ m + (n + o)
    +-assoc′ {m} {n} {o} = +-assoc m n o
    {-# REWRITE +-assoc′ #-}

  ++-assoc : ∀ (as₁ : Vec A m) (as₂ : Vec A n) (as₃ : Vec A o)
           → (as₁ ++ as₂) ++ as₃ ≡ as₁ ++ (as₂ ++ as₃)
  ++-assoc [] as₂ as₃ = refl
  ++-assoc (x ∷ as₁) as₂ as₃
    rewrite (++-assoc as₁ as₂ as₃) = refl

-- I'd like to move ++-assoc to another module (e.g., Misc), but when I do so, I
-- get an internal error. TODO: File a bug report.

-}

{-

module _ where

  private
    -- Trick to work avoid need for heterogeneous equality
    -- Sadly, it triggers an internal error.

    +-assoc′ : ∀ (m n o : ℕ) → (m + n) + o ≡ m + (n + o)
    +-assoc′ = +-assoc
    {-# REWRITE +-assoc′ #-}

  flat≡flatten++ : ∀ (u : T A n) (as : Vec A m) → flat u as ≡ flatten u ++ as
  flat≡flatten++ (lf x) as = refl
  flat≡flatten++ (nd u v) as =
    begin
      flat (nd u v) as
        ≡⟨⟩
      flat u (flat v as)
        ≡⟨ cong (flat u) (flat≡flatten++ v as) ⟩
      flat u (flatten v ++ as)
        ≡⟨ flat≡flatten++ u (flatten v ++ as) ⟩
      flatten u ++ (flatten v ++ as)
        ≡˘⟨ ++-assoc u v as ⟩
      (flatten u ++ flatten v) ++ as
        ≡⟨⟩
      flatten (nd u v) ++ as
        ∎

-- I need ++-assoc, defined in Data.Vec.Properties.WithK, but that property
-- relies on *heterogeneous* equality.

-}

map : (A → B) → T A n → T B n
map f (lf x)   = lf (f x)
map f (nd u v) = nd (map f u) (map f v)

fold : (A → A → A) → T A n → A
fold _∙_ (lf x) = x
fold _∙_ (nd u v) = fold _∙_ u ∙ fold _∙_ v

flatten∘map : ∀ (f : A → B) (t : T A n)
            → flatten (map f t) ≡ Vec.map f (flatten t)
flatten∘map f (lf x) = refl≡
flatten∘map f (nd u v)
  -- relies on {-# REWRITE map-++ #-} in Misc
  rewrite flatten∘map f u | flatten∘map f v = refl≡

-- -- Written out
-- flatten∘map f (lf x) = refl
-- flatten∘map f (nd u v) =
--   begin
--     flatten (map f (nd u v))
--       ≡⟨⟩
--     flatten (nd (map f u) (map f v))
--       ≡⟨⟩
--     flatten (map f u) ++ flatten (map f v)
--       ≡⟨ cong₂ _++_ (flatten∘map f u) (flatten∘map f v) ⟩
--     Vec.map f (flatten u) ++ Vec.map f (flatten v)
--       ≡⟨ map-++ f (flatten u) (flatten v) ⟩
--     Vec.map f (flatten (nd u v))
--       ∎

-- flatten∘fold : ∀ (_∙_ : A → A → A) (t : T A n)
--              → fold _∙_ t ≡ foldr₁ _∙_ (flatten t)
-- flatten∘fold _∙_ t = ?

-- 2 ^ n != suc _n_202 of type ℕ
-- when checking that the inferred type of an application
--   Vec A (2 ^ n)
-- matches the expected type
--   Vec A (suc _n_202)

-- I think I need an associative fold anyway.

open import Algebra.Bundles

module _ {c ℓ} (M : Monoid c ℓ) where

  open Monoid M renaming (Carrier to C)

  open import Relation.Binary.Reasoning.Setoid (setoid)

  foldV : Vec C n → C
  foldV [] = ε
  foldV (c ∷ cs) = c ∙ foldV cs

  foldV-∙ : ∀ (cs₁ : Vec C m) (cs₂ : Vec C n)
          → foldV cs₁ ∙ foldV cs₂ ≈ foldV (cs₁ ++ cs₂)
  foldV-∙ [] cs₂ = identityˡ (foldV cs₂)
  foldV-∙ (x ∷ cs₁) cs₂ =
    begin
      (x ∙ foldV cs₁) ∙ foldV cs₂ ≈⟨ assoc x (foldV cs₁) (foldV cs₂) ⟩
      x ∙ (foldV cs₁ ∙ foldV cs₂) ≈⟨ ∙-congˡ (foldV-∙ cs₁ cs₂) ⟩
      x ∙ foldV (cs₁ ++ cs₂)    ∎

  foldT : T C n → C
  foldT (lf x) = x
  foldT (nd u v) = foldT u ∙ foldT v

  foldTV : ∀ (t : T C n) → foldT t ≈ foldV (flatten t)
  foldTV (lf x) = sym (identityʳ x)

  foldTV (nd u v) =
    begin
        foldT u ∙ foldT v
      ≈⟨ ∙-cong (foldTV u) (foldTV v) ⟩
        foldV (flatten u) ∙ foldV (flatten v)
      ≈⟨ foldV-∙ (flatten u) (flatten v) ⟩
        foldV (flatten u ++ flatten v)
      ∎

  
