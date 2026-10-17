module Examples.ILL where

-- standard-library
open import Data.Nat.Base using (ℕ)
open import Data.List.Base using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Data.Product using (_,_)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥)

-- agda-np
open import Data.List.Cover

-- agda-np examples
open import Examples.ILL.Env

------------------------------------------------------------------------
-- Types

data Ty : Set where
  bsc : ℕ → Ty        -- enumerable collection of basis types
  fun : Ty → Ty → Ty  -- function type

-- context is a list of types.
Ctx = List Ty

private
  variable
    A B C : Ty
    Γ Γ₁ Γ₂ Δ  : Ctx

------------------------------------------------------------------------
-- Terms

data Tm : Ctx → Ty → Set where
  -- some global terms; postulates
  pst : ℕ → (A : Ty) → Tm [] A

  -- variables are in a singleton context
  var : Tm (A ∷ []) A

  -- function application / elimination
  -- cover splits Γ context into two parts, for the function and the argument
  app : Cover Γ Γ₁ Γ₂ → Tm Γ₁ (fun A B) → Tm Γ₂ A → Tm Γ B

  -- function introduction
  lam : Tm (A ∷ Γ) B → Tm Γ (fun A B)

-- Note: unlike STLC, this encoding of ILL terms *dictates* the context.
-- i.e. context is determined by the term.
--

private
  _~>_ = fun
  infixr 4 _~>_

id-Tm : Tm [] (A ~> A)
id-Tm = lam var

flip-Tm : Tm [] ((A ~> B ~> C) ~> (B ~> A ~> C))
flip-Tm = lam (lam (lam (app (inl (inr (inl nil))) (app (cov₁ inrlⁿ) var var) var)))

compose-Tm : Tm [] ((B ~> C) ~> (A ~> B) ~> (A ~> C))
compose-Tm = lam (lam (lam (app (inr (inr (inl nil))) var (app (cov₁ inrlⁿ) var var))))

------------------------------------------------------------------------
-- Substitution

Sub = Env Tm

-- TODO: move to .Cover.Properties
inv-inrⁿ₁ : Cover₁ Γ [] Δ → Γ ≡ Δ
inv-inrⁿ₁ inrlⁿ    = refl
inv-inrⁿ₁ (inr₁ c) = cong (_∷_ _) (inv-inrⁿ₁ c)

inv-inrⁿ : Cover Γ [] Δ → Γ ≡ Δ
inv-inrⁿ inlⁿ     = refl
inv-inrⁿ (cov₁ c) = inv-inrⁿ₁ c

-- Substitition for cover-defined terms doesn't need weakening
-- in fact we CAN NOT weaken terms :)

-- flipped argument order to make exact split
sub-Tm' : Tm Γ A → Env Tm Γ Δ → Tm Δ A
sub-Tm' (pst x A) [] = pst x A
sub-Tm' var (snoc c [] t) with inv-inrⁿ c
... | refl = t
sub-Tm' (app c f t) env with splitEnv env c
... | _ , _ , c' , env₁ , env₂ = app c' (sub-Tm' f env₁) (sub-Tm' t env₂)
sub-Tm' (lam t) env = lam (sub-Tm' t (snoc (cov₁ inrlⁿ) env var))

sub-Tm : Env Tm Γ Δ → Tm Γ A → Tm Δ A
sub-Tm env t = sub-Tm' t env

------------------------------------------------------------------------
-- Normal forms

data Nf : Ctx → Ty → Set
data Ne : Ctx → Ty → Set

data Nf where
  lamₙ : Nf (A ∷ Γ) B → Nf Γ (fun A B)
  neu  : Ne Γ A → Nf Γ A

data Ne where
  pstₙ : ℕ → (A : Ty) → Ne Γ A
  varₙ : Ne (A ∷ []) A
  appₙ : Cover Γ Γ₁ Γ₂ → Ne Γ₁ (fun A B) → Nf Γ₂ A → Ne Γ B

------------------------------------------------------------------------
-- Semantic terms; values

Val  : Ctx → Ty → Set
Val₁ : Ctx → Ty → Set

Val₁ Γ (bsc _)   = ⊥ -- no introduction terms for postulates
Val₁ Γ (fun A B) = (Δ Ω : Ctx) → Cover Δ Γ Ω → Val Ω A → Val Δ B

Val Γ A = Ne Γ A ⊎ Val₁ Γ A

------------------------------------------------------------------------
-- Evaluation

EvalEnv = Env Val

lower  : Val  Γ A → Nf Γ A
lower₁ : Val₁ Γ A → Nf Γ A

lower (inj₁ t) = neu t
lower (inj₂ t) = lower₁ t

lower₁ {A = bsc _} ()
lower₁ {A = fun A B} f = lamₙ (lower (f (A ∷ _) (A ∷ []) (cov₁ inrlⁿ) (inj₁ varₙ)))

app-val : Cover Γ Γ₁ Γ₂ → Val Γ₁ (fun A B) → Val Γ₂ A → Val Γ B
app-val c (inj₁ f) t = inj₁ (appₙ c f (lower t))
app-val c (inj₂ f) t = f _ _ c t

eval' : Tm Γ A → EvalEnv Γ Δ → Val Δ A
eval' (pst x A)   []             = inj₁ (pstₙ x A)
eval' var         (snoc c [] t)
  with inv-inrⁿ c
... | refl                       = t
eval' (app c f t) env
  with splitEnv env c
... | _ , _ , c' , env₁ , env₂   = app-val c' (eval' f env₁) (eval' t env₂)
eval' (lam f)     env            = inj₂ λ Δ Ω c t → eval' f (snoc c env t)

eval : EvalEnv Γ Δ → Tm Γ A → Val Δ A
eval env t = eval' t env

normalise-closed : Tm [] A → Nf [] A
normalise-closed t = lower (eval [] t)

_ : normalise-closed (id-Tm {A = A}) ≡ lamₙ (neu varₙ)
_ = refl

_ : normalise-closed (app nil (app nil (compose-Tm {B = B}) id-Tm) id-Tm) ≡ lamₙ (neu varₙ)
_ = refl
