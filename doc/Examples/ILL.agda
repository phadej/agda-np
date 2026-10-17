module Examples.ILL where

-- standard-library
open import Data.Nat.Base using (ℕ)
open import Data.List.Base using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Data.Product using (_,_)

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
