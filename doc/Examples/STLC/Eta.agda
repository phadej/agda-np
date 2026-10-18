module Examples.STLC.Eta where

-- standard-library
open import Data.Nat.Base using (ℕ)
open import Data.List.Base using (List; []; _∷_)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

-- agda-np
open import Data.Idx using (Idx; zero; suc)
open import Data.NP using (NP; []; _∷_) renaming (map to mapNP; lookup to lookupNP)
open import Data.NP.Wk using (Wk; wk; id; _⨟_; wk-idx; keep; wk-np)

-- agda-np Examples
open import Examples.STLC as STLC using (Ty; bsc; fun; Ctx; Tm; pst; var; app; lam; Env)

private
  variable
    A B C : Ty
    Γ Δ Ω : Ctx

------------------------------------------------------------------------
-- NbE with eta-expansion

-- comments are mostly about difference between Examples.STLC 'no-eta"
-- and this (more standard?) variant.

-- These definitions are amended.
-- Here, not all neutral forms are normal forms.
-- Only neutral forms at non function type are normal forms.
--
-- We can however have neutral form of a function type
-- inside the neutral form.
--
data Nf : Ctx → Ty → Set
data Ne : Ctx → Ty → Set

data not-fun : Ty → Set where
  nf-bsc : (n : ℕ) → not-fun (bsc n)

data Nf where
  lamₙ : Nf (A ∷ Γ) B → Nf Γ (fun A B)
  neu  : not-fun A →  Ne Γ A → Nf Γ A

data Ne where
  pstₙ : ℕ → (A : Ty) → Ne Γ A
  varₙ : Idx A Γ → Ne Γ A
  appₙ : Ne Γ (fun A B) → Nf Γ A → Ne Γ B

wk-Nf : Wk Γ Δ → Nf Γ A → Nf Δ A
wk-Ne : Wk Γ Δ → Ne Γ A → Ne Δ A

wk-Nf δ (lamₙ t)   = lamₙ (wk-Nf (keep δ) t)
wk-Nf δ (neu p t)  = neu p (wk-Ne δ t)
wk-Ne δ (pstₙ x A) = pstₙ x A
wk-Ne δ (varₙ x)   = varₙ (wk-idx δ x)
wk-Ne δ (appₙ f t) = appₙ (wk-Ne δ f) (wk-Nf δ t)

-- Semantic value is defined directly as a function of type
-- Note, there are no neutral values at function type,
-- which "forces" us to do eta-expansion
Val  : Ctx → Ty → Set
Val Γ (bsc n)   = Ne Γ (bsc n)
Val Γ (fun A B) = (Δ : Ctx) → Wk Γ Δ → Val Δ A → Val Δ B

wk-Val  : Wk Γ Δ → Val Γ A → Val Δ A
wk-Val {A = bsc _}   δ  t        = wk-Ne δ t
wk-Val {A = fun A B} δ₁ f Δ δ₂ t = f Δ (δ₁ ⨟ δ₂) t

EvalEnv = Env Val

-- In this variant, raise and lower are mutually recursive functions.
raise : Ne Γ A → Val Γ A
lower : Val Γ A → Nf Γ A

raise {A = bsc x}   f = f
raise {A = fun A B} f = λ Δ δ t → raise (appₙ (wk-Ne δ f) (lower t))

lower {A = bsc x}   t = neu (nf-bsc x) t
lower {A = fun A B} f = lamₙ (lower (f (_ ∷ _) wk (raise (varₙ zero))))

val-app : Val Γ (fun A B) → Val Γ A → Val Γ B
val-app f t = f _ id t

eval : EvalEnv Γ Δ → Tm Γ A → Val Δ A
eval env (pst x A)  = raise (pstₙ x A)
eval env (var x)    = lookupNP env x
eval env (app f t)  = val-app (eval env f) (eval env t)
eval env (lam t)    = λ Δ δ s → eval (s ∷ (mapNP (wk-Val δ) env)) t
