{-# OPTIONS --safe #-}
module Data.NP.Wk.Base where

-- standard-library
open import Level using (Level)
open import Data.List.Base using (List; []; _∷_)

-- agda-np
open import Data.Idx.Base using (Idx; zero; suc)
open import Data.NP.Base using (NP; []; _∷_)

private
  variable
    a b c : Level
    A : Set a

    F : A → Set b
    x : A
    xs ys zs : List A

------------------------------------------------------------------------
-- Types

data Wk₁ {A : Set a} : List A → List A → Set where
  wk₁   : ∀ {x xs} →                Wk₁      xs  (x ∷ xs)
  keep₁ : ∀ {x xs ys} → Wk₁ xs ys → Wk₁ (x ∷ xs) (x ∷ ys)
  skip₁ : ∀ {x xs ys} → Wk₁ xs ys → Wk₁      xs  (x ∷ ys)

data Wk {A : Set a} : List A → List A → Set where
  id : ∀ {xs} → Wk xs xs
  ne : ∀ {xs ys} → (δ : Wk₁ xs ys) → Wk xs ys

------------------------------------------------------------------------
-- Constructing Wk

pattern wk = ne wk₁

skip : Wk xs ys → Wk xs (x ∷ ys)
skip id     = wk
skip (ne δ) = ne (skip₁ δ)

keep : Wk xs ys → Wk (x ∷ xs) (x ∷ ys)
keep id     = id
keep (ne δ) = ne (keep₁ δ)

------------------------------------------------------------------------
-- Basic operations

-- Composition

infixr 4 _⨟₁_ _⨟_

_⨟₁_ : Wk₁ xs ys → Wk₁ ys zs → Wk₁ xs zs
δ₁       ⨟₁ wk₁      = skip₁ δ₁
δ₁       ⨟₁ skip₁ δ₂ = skip₁ (δ₁ ⨟₁ δ₂)
wk₁      ⨟₁ keep₁ δ₂ = skip₁ δ₂
keep₁ δ₁ ⨟₁ keep₁ δ₂ = keep₁ (δ₁ ⨟₁ δ₂)
skip₁ δ₁ ⨟₁ keep₁ δ₂ = skip₁ (δ₁ ⨟₁ δ₂)

_⨟_ : Wk xs ys → Wk ys zs → Wk xs zs
id    ⨟ id    = id
id    ⨟ ne δ₂ = ne δ₂
ne δ₁ ⨟ id    = ne δ₁
ne δ₁ ⨟ ne δ₂ = ne (δ₁ ⨟₁ δ₂)

-- Weakening indices

wk₁-idx : Wk₁ xs ys → Idx x xs → Idx x ys
wk₁-idx wk₁       i       = suc i
wk₁-idx (skip₁ δ) i       = suc (wk₁-idx δ i)
wk₁-idx (keep₁ δ) zero    = zero
wk₁-idx (keep₁ δ) (suc i) = suc (wk₁-idx δ i)

wk-idx : Wk xs ys → Idx x xs → Idx x ys
wk-idx id     i = i
wk-idx (ne δ) i = wk₁-idx δ i

-- Contracting NP

wk₁-np : Wk₁ xs ys → NP F ys → NP F xs
wk₁-np wk₁       (y ∷ ys) = ys
wk₁-np (keep₁ δ) (y ∷ ys) = y ∷ wk₁-np δ ys
wk₁-np (skip₁ δ) (y ∷ ys) = wk₁-np δ ys

wk-np : Wk xs ys → NP F ys → NP F xs
wk-np id     ys = ys
wk-np (ne δ) ys = wk₁-np δ ys
