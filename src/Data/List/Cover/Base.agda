{-# OPTIONS --safe --without-K #-}
module Data.List.Cover.Base where

-- standard-library
open import Data.List.Base as L using (List; []; _∷_)
open import Level using (Level; _⊔_)
open import Data.Product.Base using (Σ; _,_; _×_; ∃)

-- agda-np
open import Data.NP.Base using (NP; []; _∷_)
open import Data.NP.Wk.Base using (Wk; id; ne; Wk₁; wk₁; keep₁; skip₁)

private
  variable
    a b c : Level
    A : Set a

    F : A → Set b
    G : A → Set c

    x y : A
    xs ys zs xys yzs xzs xyzs : List A

------------------------------------------------------------------------
-- Types

data Cover₁ {A : Set a} : List A → List A → List A → Set a where
  inrlⁿ : ∀ {x xs}                           → Cover₁ (x ∷ xs)       xs (x ∷ [])
  inl₁  : ∀ {x xys xs ys} → Cover₁ xys xs ys → Cover₁ (x ∷ xys) (x ∷ xs)     ys
  inr₁  : ∀ {y xys xs ys} → Cover₁ xys xs ys → Cover₁ (y ∷ xys)      xs (y ∷ ys)

-- Inspired by
--
-- @article{McBride_2018,
--    title={Everybody’s Got To Be Somewhere},
--    volume={275},
--    ISSN={2075-2180},
--    url={http://dx.doi.org/10.4204/EPTCS.275.6},
--    DOI={10.4204/eptcs.275.6},
--    journal={Electronic Proceedings in Theoretical Computer Science},
--    publisher={Open Publishing Association},
--    author={McBride, Conor},
--    year={2018},
--    month=July, pages={53–69} }
--
data Cover {A : Set a} : List A → List A → List A → Set a where
  inlⁿ : ∀ {xs}                           → Cover xs  xs []
  cov₁ : ∀ {xys xs ys} → Cover₁ xys xs ys → Cover xys xs ys

------------------------------------------------------------------------
-- Basic operations

nil : Cover {A = A} [] [] []
nil = inlⁿ

inl : Cover xys xs ys → Cover (x ∷ xys) (x ∷ xs) ys
inl inlⁿ     = inlⁿ
inl (cov₁ c) = cov₁ (inl₁ c)

inr' : Cover xys xs ys → Cover₁ (y ∷ xys) xs (y ∷ ys)
inr' inlⁿ     = inrlⁿ
inr' (cov₁ c) = inr₁ c

inr : Cover xys xs ys → Cover (y ∷ xys) xs (y ∷ ys)
inr c = cov₁ (inr' c)

inrⁿ₁ : Cover₁ xys xs ys → Cover₁ ys [] ys
inrⁿ₁ inrlⁿ    = inrlⁿ
inrⁿ₁ (inl₁ c) = inrⁿ₁ c
inrⁿ₁ (inr₁ c) = inr₁ (inrⁿ₁ c)

-- this can be implementing using induction on ys
-- but often there is Cover _ _ ys around which can be used instead
-- allowing ys to be erased (in Haskell translations)
inrⁿ : Cover xys xs ys → Cover ys [] ys
inrⁿ inlⁿ     = inlⁿ
inrⁿ (cov₁ c) = cov₁ (inrⁿ₁ c)

-- Converting to Wk

cover-wk₁₁ : Cover₁ xys xs ys → Wk₁ xs xys
cover-wk₁₁ inrlⁿ    = wk₁
cover-wk₁₁ (inl₁ c) = keep₁ (cover-wk₁₁ c)
cover-wk₁₁ (inr₁ c) = skip₁ (cover-wk₁₁ c)

cover-wk₁ : Cover xys xs ys → Wk xs xys
cover-wk₁ inlⁿ     = id
cover-wk₁ (cov₁ c) = ne (cover-wk₁₁ c)

-- cover­wk₂ needs to construct Wk [] ys out of a thin air

-- Splitting NP

split₁ : Cover₁ xys xs ys → NP F xys → NP F xs × NP F ys
split₁ inrlⁿ (x ∷ xys) = xys , x ∷ []
split₁ (inl₁ c) (x ∷ xys) with split₁ c xys
... | xs , ys = x ∷ xs , ys
split₁ (inr₁ c) (y ∷ xys) with split₁ c xys
... | xs , ys = xs , y ∷ ys

split : Cover xys xs ys → NP F xys → NP F xs × NP F ys
split inlⁿ     xys = xys , []
split (cov₁ c) xys = split₁ c xys

-- reassocication of covers

-- Cover is kind of associative and commutative
-- the assoc is defined below.

-- (xs <> ys) <> zs = xs <> (ys <> zs)
assoc₁
  : Cover₁ xyzs xys zs → Cover₁ xys xs ys
  → ∃ λ yzs → Cover₁ xyzs xs yzs × Cover₁ yzs ys zs
assoc₁ inrlⁿ     c₂ = _ ∷ _ , inr₁ c₂ , inrlⁿ
assoc₁ (inr₁ c₁) c₂ with assoc₁ c₁ c₂
... | yzs' , c₁' , c₂' = _ ∷ yzs' , inr₁ c₁' , inr₁ c₂'
assoc₁ (inl₁ c₁) inrlⁿ = _ , inr₁ c₁ , inl₁ (inrⁿ₁ c₁)
assoc₁ (inl₁ c₁) (inl₁ c₂) with assoc₁ c₁ c₂
... | yzs' , c₁' , c₂' = yzs' , inl₁ c₁' , c₂'
assoc₁ (inl₁ c₁) (inr₁ c₂) with assoc₁ c₁ c₂
... | yzs' , c₁' , c₂' = _ ∷ yzs' , inr₁ c₁' , inl₁ c₂'

-- (xs <> ys) <> zs = xs <> (ys <> zs)
assoc
   : Cover xyzs xys zs → Cover xys xs ys
   → ∃ λ yzs → Cover xyzs xs yzs × Cover yzs ys zs
assoc inlⁿ      c₂    = _ , c₂ , inlⁿ
assoc (cov₁ c₁) inlⁿ  = _ , cov₁ c₁ , cov₁ (inrⁿ₁ c₁)
assoc (cov₁ c₁) (cov₁ c₂) with assoc₁ c₁ c₂
... | yzs , c₁' , c₂' = yzs , cov₁ c₁' , cov₁ c₂'

-- xs <> (ys <> zs) = (xs <> ys) <> zs
unassoc₁
  : Cover₁ xyzs xs yzs → Cover₁ yzs ys zs
  → ∃ λ xys → Cover₁ xyzs xys zs × Cover xys xs ys
unassoc₁ inrlⁿ inrlⁿ = _ , inrlⁿ , inlⁿ
unassoc₁ (inl₁ c₁) c₂ with unassoc₁ c₁ c₂
... | xys' , c₁' , c₂' = _ ∷ xys' , inl₁ c₁' , inl c₂'
unassoc₁ (inr₁ c₁) inrlⁿ = _ , inrlⁿ , cov₁ c₁
unassoc₁ (inr₁ c₁) (inl₁ c₂) with unassoc₁ c₁ c₂
... | xys' , c₁' , c₂' = _ ∷ xys' , inl₁ c₁' , inr c₂'
unassoc₁ (inr₁ c₁) (inr₁ c₂) with unassoc₁ c₁ c₂
... | xys' , c₁' , c₂' = xys' , inr₁ c₁' , c₂'

-- xs <> (ys <> zs) = (xs <> ys) <> zs
unassoc
  : Cover xyzs xs yzs → Cover yzs ys zs
  → ∃ λ xys → Cover xyzs xys zs × Cover xys xs ys
unassoc inlⁿ      inlⁿ  = _ , inlⁿ , inlⁿ
unassoc (cov₁ c₁) inlⁿ  = _ , inlⁿ , cov₁ c₁
unassoc (cov₁ c₁) (cov₁ c₂) with unassoc₁ c₁ c₂
... | xys' , c₁' , c₂' = xys' , cov₁ c₁' , c₂'

-- However it is impossible (?) to define
--
-- comm : Cover xys xs ys → Cover xys ys xs
--
-- without pattern matching on xys (or ys)
--
-- comm inlⁿ = inrⁿ -- would match on the index list
--
-- Yet, the situation is not all that bad.
-- Some combinations of assoc and comm
-- are still definable without pattern matching
-- on the indices (i.e. keeping them erasable)
-- when there is extra data, e.g. another
-- cover with matching indices.
-- (See assoc for an example of that).
--
-- There 6 ways to permute three arguments
-- which are listed below
--
-- xs ys zs -> xs ys zs  -- (1, 2, 3)
--             xs zs ys  -- (1, 3, 2)
--             ys xs zs  -- (2, 1, 3)
--             ys zs xs  -- (2, 3, 1)
--             zs xs ys  -- (3, 1, 2)
--             zs ys xs  -- (3, 2, 1)
--
-- See https://en.wikipedia.org/wiki/Permutation
--
-- and we can reassociate (xs <> ys) <> zs, or not.
--
-- So there are twelve potential functions
-- (assoc and unassoc being two).
--
-- I only needed one additional one, so I only defined it.
-- (I'm not sure all are definable without pattern matching on indices).
-- The naming scheme is hopefully self-explanatory.

-- (xs <> ys) <> zs  -> (xs <> zs) <> ys
permute-132₁
   : Cover₁ xyzs xys zs → Cover₁ xys xs ys
   → ∃ λ xzs → Cover₁ xyzs xzs ys × Cover₁ xzs xs zs
permute-132₁ inrlⁿ     c₂ = _ ∷ _ , inl₁ c₂ , inrlⁿ
permute-132₁ (inr₁ c₁) c₂ with permute-132₁ c₁ c₂
... | xzs' , c₁' , c₂' = _ ∷ xzs' , inl₁ c₁' , inr₁ c₂'
permute-132₁ (inl₁ c₁) inrlⁿ = _ , inrlⁿ , c₁
permute-132₁ (inl₁ c₁) (inl₁ c₂) with permute-132₁ c₁ c₂
... | xzs' , c₁' , c₂' = _ ∷ xzs' , inl₁ c₁' , inl₁ c₂'
permute-132₁ (inl₁ c₁) (inr₁ c₂) with permute-132₁ c₁ c₂
... | xzs' , c₁' , c₂' = xzs' , inr₁ c₁' , c₂'

-- (xs <> ys) <> zs  -> (xs <> zs) <> ys
permute-132
   : Cover xyzs xys zs → Cover xys xs ys
   → ∃ λ xzs → Cover xyzs xzs ys × Cover xzs xs zs
permute-132 inlⁿ      c₂   = _ , c₂ , inlⁿ
permute-132 (cov₁ c₁) inlⁿ = _ , inlⁿ , cov₁ c₁
permute-132 (cov₁ c₁) (cov₁ c₂) with permute-132₁ c₁ c₂
... | xzs' , c₁' , c₂' = xzs' , cov₁ c₁' , cov₁ c₂'
