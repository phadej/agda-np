{-# OPTIONS --safe --without-K #-}
module Data.List.Cover.Base where

-- standard-library
open import Data.List.Base as L using (List; []; _∷_)
open import Level using (Level; _⊔_)
open import Data.Product.Base using (Σ; _,_; _×_; ∃)

-- agda-np
open import Data.NP.Base using (NP; []; _∷_)

private
  variable
    a b c : Level
    A : Set a

    F : A → Set b
    G : A → Set c

    x y : A
    xs ys zs xys xyzs : List A

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

inr : Cover xys xs ys → Cover (y ∷ xys) xs (y ∷ ys)
inr inlⁿ     = cov₁ inrlⁿ
inr (cov₁ c) = cov₁ (inr₁ c)

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
assoc           inlⁿ      c₂       = _  , c₂      , inlⁿ
assoc {zs = zs} (cov₁ c₁) inlⁿ     = zs , cov₁ c₁ , cov₁ (inrⁿ₁ c₁)
assoc           (cov₁ c₁) (cov₁ c₂) with assoc₁ c₁ c₂
... | yzs , c₁' , c₂' = yzs , cov₁ c₁' , cov₁ c₂'

-- (xs <> ys) <> zs  -> (xs <> zs) <> ys
assoc-a₁
   : Cover₁ xyzs xys zs → Cover₁ xys xs ys
   → ∃ λ xzs → Cover₁ xyzs xzs ys × Cover₁ xzs xs zs
assoc-a₁ inrlⁿ c₂ = _ ∷ _ , inl₁ c₂ , inrlⁿ
assoc-a₁ (inr₁ c₁) c₂ with assoc-a₁ c₁ c₂
... | xzs' , c₁' , c₂' = _ ∷ xzs' , inl₁ c₁' , inr₁ c₂'
assoc-a₁ (inl₁ c₁) inrlⁿ = _ , inrlⁿ , c₁
assoc-a₁ (inl₁ c₁) (inl₁ c₂) with assoc-a₁ c₁ c₂
... | xzs' , c₁' , c₂' = _ ∷ xzs' , inl₁ c₁' , inl₁ c₂'
assoc-a₁ (inl₁ c₁) (inr₁ c₂) with assoc-a₁ c₁ c₂
... | xzs' , c₁' , c₂' = xzs' , inr₁ c₁' , c₂'

-- (xs <> ys) <> zs  -> (xs <> zs) <> ys
assoc-a
   : Cover xyzs xys zs → Cover xys xs ys
   → ∃ λ xzs → Cover xyzs xzs ys × Cover xzs xs zs
assoc-a inlⁿ xys=xs+ys = _ , xys=xs+ys , inlⁿ
assoc-a (cov₁ c₁) inlⁿ = _ , inlⁿ , cov₁ c₁
assoc-a (cov₁ c₁) (cov₁ c₂) with assoc-a₁ c₁ c₂
... | xzs' , c₁' , c₂' = xzs' , cov₁ c₁' , cov₁ c₂'

-- (xs <> ys) <> zs -> xs <> (ys <> zs)
assoc-b₁
   : Cover₁ xyzs xys zs → Cover₁ xys xs ys
   → ∃ λ yzs → Cover₁ xyzs xs yzs × Cover₁ yzs ys zs
assoc-b₁ inrlⁿ c₂ = _ ∷ _ , inr₁ c₂ , inrlⁿ
assoc-b₁ (inr₁ c₁) c₂ with assoc-b₁ c₁ c₂
... | yzs , c₁' , c₂' = _ ∷ yzs , inr₁ c₁' , inr₁ c₂'
assoc-b₁ {zs = zs} (inl₁ c₁) inrlⁿ = _ ∷ zs , inr₁ c₁ , inl₁ (inrⁿ₁ c₁)
assoc-b₁ (inl₁ c₁) (inl₁ c₂) with assoc-b₁ c₁ c₂
... | yzs , c₁' , c₂' = yzs , inl₁ c₁' , c₂'
assoc-b₁ (inl₁ c₁) (inr₁ c₂) with assoc-b₁ c₁ c₂
... | yzs , c₁' , c₂' = _ ∷ yzs , inr₁ c₁' , inl₁ c₂'

-- (xs <> ys) <> zs -> xs <> (ys <> zs)
assoc-b
   : Cover xyzs xys zs → Cover xys xs ys
   → ∃ λ yzs → Cover xyzs xs yzs × Cover yzs ys zs
assoc-b           inlⁿ      c₂         = _  , c₂      , inlⁿ
assoc-b {zs = zs} (cov₁ c₁) inlⁿ       = zs , cov₁ c₁ , cov₁ (inrⁿ₁ c₁)
assoc-b           (cov₁ c₁) (cov₁ c₂) with assoc-b₁ c₁ c₂
... | yzs , c₁' , c₂' = yzs , cov₁ c₁' , cov₁ c₂'
