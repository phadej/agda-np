module Examples.ILL.Env where

-- standard library
open import Level using (Level; _⊔_)
open import Data.List using (List; []; _∷_)
open import Data.Product.Base using (Σ; _,_; _×_; ∃; ∃₂)

-- agda-np
open import Data.List.Cover

private
  variable
    a b : Level
    A : Set a

    x y : A
    xs ys xys xys' : List A

-- TODO: I'm not happy with snoc constructor name
data Env {A : Set a} (F : List A → A → Set b) : List A → List A → Set (a ⊔ b) where
  []   : Env F [] []
  snoc : Cover xys' xs ys -> Env F xys xs -> F ys y -> Env F (y ∷ xys) xys'

splitEnv₁
  : {F : List A → A → Set b} → Env F xys xys' → Cover₁ xys xs ys
  → ∃₂ λ xs' ys' → Cover xys' xs' ys' × Env F xs xs' × Env F ys ys'
splitEnv₁ (snoc c₁ env t) inrlⁿ = _ , _ , c₁ , env , snoc (inrⁿ c₁) [] t
splitEnv₁ (snoc c₁ env t) (inl₁ c₂) with splitEnv₁ env c₂
... | xs' , ys' , c₃ , env₁ , env₂ with assoc-a c₁ c₃
... | xzs' , c₄ , c₅ = xzs' , ys' , c₄ , snoc c₅ env₁ t , env₂
splitEnv₁ (snoc c₁ env t) (inr₁ c₂) with splitEnv₁ env c₂
... | xs' , ys' , c₃ , env₁ , env₂ with assoc-b c₁ c₃
... | yzs , c₄ , c₅  = xs' , yzs , c₄ , env₁ , snoc c₅ env₂ t

splitEnv
  : {F : List A → A → Set b} → Env F xys xys' → Cover xys xs ys
  → ∃₂ λ xs' ys' → Cover xys' xs' ys' × Env F xs xs' × Env F ys ys'
splitEnv env inlⁿ = _ , [] , inlⁿ , env , []
splitEnv env (cov₁ c₂) = splitEnv₁ env c₂
