{-# OPTIONS --safe --without-K #-}
-- Simpler version of Data.List.Membership.Setoid
module Data.Idx.Base where

-- standard-library
open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.List.Base using (List; []; _∷_)
open import Level using (Level; _⊔_)

private
  variable
    a b : Level
    A : Set a
    B : Set b

    xs : List A

------------------------------------------------------------------------
-- Types

-- Index into a list
data Idx {A : Set a} (x : A) : List A → Set a where
  zero : ∀ {xs} → Idx x (x ∷ xs)
  suc  : ∀ {xs y} → Idx x xs → Idx x (y ∷ xs)

-- A conversion: toℕ "i" = i.
toℕ : Idx A xs → ℕ
toℕ zero    = zero
toℕ (suc i) = suc (toℕ i)

------------------------------------------------------------------------
-- Basic operations

-- lookup : Vec A n → Fin n → A
