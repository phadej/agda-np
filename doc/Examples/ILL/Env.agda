module Examples.ILL.Env where

-- standard library
open import Level using (Level; _⊔_)
open import Data.List using (List; []; _∷_)
open import Data.Product.Base using (Σ; _,_; _×_; ∃; ∃₂)

-- agda-np
open import Data.List.Cover.Base
open import Data.NP.Wk.Base

private
  variable
    a b : Level
    A : Set a

    x y : A
    xs xs' ys xys xys' : List A

    F : List A → A → Set b

-- TODO: I'm not happy with snoc constructor name
data Env {A : Set a} (F : List A → A → Set b) : List A → List A → Set (a ⊔ b) where
  []   : Env F [] []
  snoc : Cover xys' xs ys -> Env F xys xs -> F ys y -> Env F (y ∷ xys) xys'

splitEnv₁
  : Env F xys xys' → Cover₁ xys xs ys
  → ∃₂ λ xs' ys' → Cover xys' xs' ys' × Env F xs xs' × Env F ys ys'
splitEnv₁ (snoc c₁ env t) inrlⁿ = _ , _ , c₁ , env , snoc (inrⁿ c₁) [] t
splitEnv₁ (snoc c₁ env t) (inl₁ c₂) with splitEnv₁ env c₂
... | xs' , ys' , c₃ , env₁ , env₂ with permute-132 c₁ c₃
... | xzs' , c₄ , c₅ = xzs' , ys' , c₄ , snoc c₅ env₁ t , env₂
splitEnv₁ (snoc c₁ env t) (inr₁ c₂) with splitEnv₁ env c₂
... | xs' , ys' , c₃ , env₁ , env₂ with assoc c₁ c₃
... | yzs , c₄ , c₅  = xs' , yzs , c₄ , env₁ , snoc c₅ env₂ t

splitEnv
  : Env F xys xys' → Cover xys xs ys
  → ∃₂ λ xs' ys' → Cover xys' xs' ys' × Env F xs xs' × Env F ys ys'
splitEnv env inlⁿ = _ , [] , inlⁿ , env , []
splitEnv env (cov₁ c₂) = splitEnv₁ env c₂

wk₁-env : Wk₁ xs' xs → Env F xs ys → ∃ λ ys' → Wk ys' ys × Env F xs' ys'
wk₁-env wk₁       (snoc c env t) = _ , cover-wk₁ c , env
wk₁-env (skip₁ δ) (snoc c env t) with wk₁-env δ env
... | ys' , δ' , env' = ys' , (δ' ⨟ cover-wk₁ c) , env'
wk₁-env (keep₁ δ) (snoc c env t) with wk₁-env δ env
... | _   , δ' , env' with cover⨟wk₁ c δ'
... | ys' , c' , δ'' = ys' , δ'' , snoc c' env' t

wk-env : Wk xs' xs → Env F xs ys → ∃ λ ys' → Wk ys' ys × Env F xs' ys'
wk-env id     env = _ , id , env
wk-env (ne δ) env with wk₁-env δ env
... | ys' , δ' , env' = ys' , δ' , env'
