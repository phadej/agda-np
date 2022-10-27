{-# OPTIONS --safe --without-K #-}
-- Simpler version of Setoid Data.List.Relation.Unary.All
module Data.NP.Base where

-- standard-library
open import Data.List.Base as L using (List; []; _∷_)
open import Level using (Level; _⊔_)

-- agda-np
open import Data.Idx.Base using (Idx; zero; suc)

private
  variable
    a b c : Level
    A : Set a

    F : A → Set b
    G : A → Set c

    x : A
    xs ys : List A

------------------------------------------------------------------------
-- Types

infixr 5 _∷_

data NP {A : Set a} (F : A → Set b) : List A → Set (a ⊔ b) where
  []  : NP F []
  _∷_ : ∀ {x xs} → (fx : F x) → (fxs : NP F xs) → NP F (x ∷ xs)

------------------------------------------------------------------------
-- Basic operations

lookup : NP F xs → Idx x xs → F x
lookup (x ∷ xs) zero    = x
lookup (x ∷ xs) (suc i) = lookup xs i

------------------------------------------------------------------------
-- Operations for transforming NP

map : (∀ {x} → F x → G x) → NP F xs → NP G xs
map f []       = []
map f (x ∷ xs) = f x ∷ map f xs

-- Concatenation

infixr 5 _++_

_++_ : NP F xs → NP F ys → NP F (xs L.++ ys)
[]       ++ ys = ys
(x ∷ xs) ++ ys = x ∷ xs ++ ys

------------------------------------------------------------------------
-- Operations for building NP

[_] : F x → NP F L.[ x ]
[ x ] = x ∷ []

tabulate : (∀ {x} → Idx x xs → F x) → NP F xs
tabulate {xs = []}     f = []
tabulate {xs = x ∷ xs} f = f zero ∷ tabulate (λ z → f (suc z))

allIdx : (xs : List A) → NP (λ x → Idx x xs) xs
allIdx _ = tabulate (λ i → i)
