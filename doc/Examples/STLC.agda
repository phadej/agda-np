module Examples.STLC where

-- standard-library
open import Data.Nat.Base using (ℕ)
open import Data.List.Base using (List; []; _∷_)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥)

-- agda-np
open import Data.Idx using (Idx; zero; suc)
open import Data.NP using (NP; []; _∷_) renaming (map to mapNP; lookup to lookupNP)
open import Data.NP.Wk using (Wk; wk; id; _⨟_; wk-idx; keep)

------------------------------------------------------------------------
-- Types

data Ty : Set where
  bsc : ℕ → Ty        -- enumerable collection of basis types
  fun : Ty → Ty → Ty  -- function type

-- context is a list of types.
Ctx = List Ty

private
  variable
    A B : Ty
    Γ Δ : Ctx

------------------------------------------------------------------------
-- Terms

data Tm : Ctx → Ty → Set where
  pst : ℕ → (A : Ty) → Tm Γ A              -- some global terms; postulates
  var : Idx A Γ → Tm Γ A                   -- variables
  app : Tm Γ (fun A B) → Tm Γ A → Tm Γ B   -- function application / elimination
  lam : Tm (A ∷ Γ) B → Tm Γ (fun A B)      -- function introduction

------------------------------------------------------------------------
-- Normal forms

data Nf : Ctx → Ty → Set
data Ne : Ctx → Ty → Set

data Nf where
  lamₙ : Nf (A ∷ Γ) B → Nf Γ (fun A B)
  neu  : Ne Γ A → Nf Γ A

data Ne where
  pstₙ : ℕ → (A : Ty) → Ne Γ A
  varₙ : Idx A Γ → Ne Γ A
  appₙ : Ne Γ (fun A B) → Nf Γ A → Ne Γ B

wk-Nf : Wk Γ Δ → Nf Γ A → Nf Δ A
wk-Ne : Wk Γ Δ → Ne Γ A → Ne Δ A

wk-Nf δ (lamₙ t)   = lamₙ (wk-Nf (keep δ) t)
wk-Nf δ (neu t)    = neu (wk-Ne δ t)
wk-Ne δ (pstₙ x A) = pstₙ x A
wk-Ne δ (varₙ x)   = varₙ (wk-idx δ x)
wk-Ne δ (appₙ f t) = appₙ (wk-Ne δ f) (wk-Nf δ t)

------------------------------------------------------------------------
-- Semantic terms; values

-- semantic values are a sum of neutral forms at that type and "raised" version of introduction forms.
-- it's important to NOT define Val₁ and Val as data-types (in Agda) to make termination checker happy.
--
-- In practical implementation (e.g. in Haskell) we would implement lambda terms as closures,
-- that's out of reach in Agda as far as I'm aware.
--
-- By definining semantic values outright as a disjoint union
-- * we avoid eta-expanding functions (which may or may not be desired) and
-- * make lowering/quoting and raising/lifting between semantic values and normal/neutral forms NOT recursive.
-- In fact, we don't need arbitrary lifting.
Val  : Ctx → Ty → Set
Val₁ : Ctx → Ty → Set

Val₁ Γ (bsc _)   = ⊥ -- no introduction terms for postulates
Val₁ Γ (fun A B) = (Δ : Ctx) → Wk Γ Δ → Val Δ A → Val Δ B

Val Γ A = Ne Γ A ⊎ Val₁ Γ A

wk-Val  : Wk Γ Δ → Val  Γ A → Val  Δ A
wk-Val₁ : Wk Γ Δ → Val₁ Γ A → Val₁ Δ A

wk-Val δ (inj₁ t) = inj₁ (wk-Ne δ t)
wk-Val δ (inj₂ t) = inj₂ (wk-Val₁ δ t)

wk-Val₁ {A = bsc _} _ ()
wk-Val₁ {A = fun A B} δ₁ f Δ δ₂ t = f Δ (δ₁ ⨟ δ₂) t

------------------------------------------------------------------------
-- Evaluation

-- Environments are a collection of "term-like" things in one context indexed by other.
Env : (Ctx → Ty → Set) → Ctx → Ctx → Set
Env F Γ Δ = NP (F Δ) Γ

-- e.g. Sub(stitition) is Sub = Env Tm; see below

EvalEnv = Env Val

-- lowering or quoting i.e. converting semantic values to normal forms.
--
-- Note: here (in lower₁) and in eval env (lam t) we need to weaken contexts
-- with (almost) identity weakening. This is the case where slightly
-- more complicated Wk definition pays off.
lower  : Val Γ A → Nf Γ A
lower₁ : Val₁ Γ A → Nf Γ A

lower (inj₁ t) = neu t
lower (inj₂ t) = lower₁ t

lower₁         {A = bsc x} ()
lower₁ {Γ = Γ} {A = fun A B} f = lamₙ (lower (f (A ∷ Γ) wk (inj₁ (varₙ zero))))

-- evaluation
app-val : Val Γ (fun A B) → Val Γ A → Val Γ B
app-val (inj₁ f) t = inj₁ (appₙ f (lower t))
app-val (inj₂ f) t = f _ id t

eval : EvalEnv Γ Δ → Tm Γ A → Val Δ A
eval env (pst x A) = inj₁ (pstₙ x A)
eval env (var x)   = lookupNP env x
eval env (app f t) = app-val (eval env f) (eval env t)
eval env (lam t)   = inj₂ λ Δ δ x → eval (x ∷ mapNP (wk-Val δ) env) t

normalise-closed : Tm [] A → Nf [] A
normalise-closed t = lower (eval [] t)

------------------------------------------------------------------------
-- Substition (for comparison purposes)

Sub = Env Tm

wk-Tm : Wk Γ Δ → Tm Γ A → Tm Δ A
wk-Tm δ (pst x A) = pst x A
wk-Tm δ (var x)   = var (wk-idx δ x)
wk-Tm δ (app f t) = app (wk-Tm δ f) (wk-Tm δ t)
wk-Tm δ (lam t)   = lam (wk-Tm (keep δ) t)

sub-Idx : Sub Γ Δ → Idx A Γ → Tm Δ A
sub-Idx σ i = lookupNP σ i

keep-Sub : Sub Γ Δ → Sub (A ∷ Γ) (A ∷ Δ)
keep-Sub σ = var zero ∷ mapNP (wk-Tm wk) σ

sub-Tm : Sub Γ Δ → Tm Γ A → Tm Δ A
sub-Tm σ (pst x A) = pst x A
sub-Tm σ (var x)   = sub-Idx σ x
sub-Tm σ (app f t) = app (sub-Tm σ f) (sub-Tm σ t)
sub-Tm σ (lam t)   = lam (sub-Tm (keep-Sub σ) t)
