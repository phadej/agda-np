module Examples.STLC where

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
    Γ Δ Ω : Ctx

------------------------------------------------------------------------
-- Terms

data Tm : Ctx → Ty → Set where
  pst : ℕ → (A : Ty) → Tm Γ A              -- some global terms; postulates
  var : Idx A Γ → Tm Γ A                   -- variables
  app : Tm Γ (fun A B) → Tm Γ A → Tm Γ B   -- function application / elimination
  lam : Tm (A ∷ Γ) B → Tm Γ (fun A B)      -- function introduction

private
  _~>_ : Ty → Ty → Ty
  A ~> B = fun A B
  infixr 4 _~>_

  _$_ : Tm Γ (A ~> B) → Tm Γ A → Tm Γ B
  f $ x = app f x
  infixl 0 _$_

  pattern var₀ = var zero
  pattern var₁ = var (suc zero)
  pattern var₂ = var (suc (suc zero))

id-Tm : Tm [] (A ~> A)
id-Tm = lam var₀

flip-Tm : Tm [] ((A ~> B ~> C) ~> (B ~> A ~> C))
flip-Tm = lam (lam (lam (var₂ $ var₀ $ var₁)))

compose-Tm : Tm [] ((B ~> C) ~> (A ~> B) ~> (A ~> C))
compose-Tm = lam (lam (lam (app var₂ (app var₁ var₀))))

const-Tm : Tm [] (A ~> B ~> A)
const-Tm = lam (lam var₁)

w-Tm : Tm [] ((A ~> A ~> B) ~> (A ~> B))
w-Tm = lam (lam (var₁ $ var₀ $ var₀))

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
-- it's important to NOT define Val₁ and Val as data-types (in Agda) to positivity checker happy.
--
-- In other words: it's tempting to definition of Val starting as
--
-- data Val Γ : Ty → Set where
--   vlam : ((Δ : Ctx) → Wk Γ Δ → Val' Γ A → Val' Δ B) → Val' Γ (fun A B)
--
-- but Agda will reject it.
--
-- For similar reasons we need to use neutral forms in the definition instead of delaying the conversion,
-- In Agda we need to define normal&neutral forms before we can define semantic values.
--
-- In practical implementation (e.g. in Haskell) we would implement lambda terms as closures,
-- that is also out of reach in Agda.
--
-- By definining semantic values outright as a disjoint union
--
-- * we avoid eta-expanding functions (which may or may not be desired) and
-- * make lowering/quoting and raising/lifting between semantic values and normal/neutral forms NOT recursive.
--
-- In fact, we don't need arbitrary lifting.
-- See Examples.STLC.Eta for a variant with eta-expansion.
--
-- I think this is more closely resembles actual implementations (again in Haskell).
-- There all constructors of Val and Val₁ are mushed together anyway
-- and the evaluation **is not** eta-expanding.
-- Instead we eta-expand in conversion checker, in other words only if needed.

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

-- We can trivially define raise, it's just an injection.
--
-- It is "kind of" needed to define evaluation of postulates,
-- and to raise variables in the lowering of functions.
raise : Ne Γ A → Val Γ A
raise = inj₁

-- lowering or quoting i.e. converting semantic values to normal forms.
--
-- Note: here (in lower₁) and in eval env (lam t) we need to weaken contexts
-- with (almost) identity weakening. This is the case where slightly
-- more complicated Wk definition pays off.
lower  : Val  Γ A → Nf Γ A
lower₁ : Val₁ Γ A → Nf Γ A

lower (inj₁ t) = neu t
lower (inj₂ t) = lower₁ t

lower₁         {A = bsc x} ()
lower₁ {Γ = Γ} {A = fun A B} f = lamₙ (lower (f (A ∷ Γ) wk (raise (varₙ zero))))

-- evaluation
app-val : Val Γ (fun A B) → Val Γ A → Val Γ B
app-val (inj₁ f) t = inj₁ (appₙ f (lower t))
app-val (inj₂ f) t = f _ id t

eval : EvalEnv Γ Δ → Tm Γ A → Val Δ A
eval env (pst x A) = raise (pstₙ x A)
eval env (var x)   = lookupNP env x
eval env (app f t) = app-val (eval env f) (eval env t)
eval env (lam t)   = inj₂ λ Δ δ x → eval (x ∷ mapNP (wk-Val δ) env) t

normalise-closed : Tm [] A → Nf [] A
normalise-closed t = lower (eval [] t)

_ : normalise-closed (id-Tm {A = A}) ≡ lamₙ (neu (varₙ zero))
_ = refl

_ : normalise-closed (compose-Tm {B = B} $ id-Tm $ id-Tm) ≡ lamₙ (neu (varₙ zero))
_ = refl

_ : normalise-closed (compose-Tm $ const-Tm {B = B} $ const-Tm {A = A} {B = C}) ≡ lamₙ (lamₙ (lamₙ (neu (varₙ (suc (suc zero))))))
_ = refl

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

-- substitution compositions
_ₜ⨟ₛ_ : Wk Γ Δ → Sub Δ Ω → Sub Γ Ω
δ ₜ⨟ₛ σ = wk-np δ σ

_ₛ⨟ₜ_ : Sub Γ Δ → Wk Δ Ω → Sub Γ Ω
σ ₛ⨟ₜ δ = mapNP (wk-Tm δ) σ

_⨟ₛ_ : Sub Γ Δ → Sub Δ Ω → Sub Γ Ω
σ₁ ⨟ₛ σ₂ = mapNP (sub-Tm σ₂) σ₁
