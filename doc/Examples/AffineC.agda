module Examples.AffineC where

-- standard-library
open import Data.Nat.Base using (ℕ)
open import Data.List.Base using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Data.Product using (∃; _×_; _,_)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥)

-- agda-np
open import Data.List.Cover
open import Data.NP.Wk

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
    Γ Γ₁ Γ₂ Δ Δ₁ Δ₂ : Ctx

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

  -- weakening of the context
  wkn : Wk Γ Δ → Tm Γ A → Tm Δ A

-- Note: unlike STLC, this encoding of ILL terms *dictates* the context.
-- i.e. context is determined by the term.
--

-- konst i.e. constant function application
-- can be defined used wkd
konst : Cover Γ Γ₁ Γ₂ → Tm Γ₁ A → Tm Γ₂ B → Tm Γ A
konst c x _ = wkn (cover-wk₁ c) x

-- we could also have konst as a primitive and define
-- wkd as a combinator, but that way is messier:
-- We would need to do 'konst t x' for each variable x
-- we want to forget.

-- lak i.e. lambda abstraction with unused argument
-- is admissible, wkd or konst are powerful enough to define it:
-- we immediately forget the variable introduced by lam
--
-- We could choose either lak or konst as a primitive,
-- but direct weakening with wkn is the simplest one.
lak : Tm Γ B → Tm Γ (fun A B)
lak t = lam (wkn wk t)

private
  _~>_ = fun
  infixr 4 _~>_

id-Tm : Tm [] (A ~> A)
id-Tm = lam var

flip-Tm : Tm [] ((A ~> B ~> C) ~> (B ~> A ~> C))
flip-Tm = lam (lam (lam (app (cov₁ (inl₁ inrlⁿ)) (app (cov₁ inrlⁿ) var var) var)))

compose-Tm : Tm [] ((B ~> C) ~> (A ~> B) ~> (A ~> C))
compose-Tm = lam (lam (lam (app (cov₁ (inr₁ inrlⁿ)) var (app (cov₁ inrlⁿ) var var))))

const-Tm : Tm [] (A ~> B ~> A)
const-Tm = lam (lak var)

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
sub-Tm' (wkn δ t) env with wk-env δ env
... | _ , δ' , env' = wkn δ' (sub-Tm' t env')

sub-Tm : Env Tm Γ Δ → Tm Γ A → Tm Δ A
sub-Tm env t = sub-Tm' t env

------------------------------------------------------------------------
-- Weakened

record Weakened (F : Ctx → Set) (Γ : Ctx) : Set where
  constructor weakened
  field {Ψ} : Ctx
  field δ : Wk Ψ Γ
  field t : F Ψ

wk-weakened : {F : Ctx → Set} → Wk Γ Δ → Weakened F Γ → Weakened F Δ
wk-weakened δ (weakened δ' t) = weakened (δ' ⨟ δ) t

unweaken : {F : Ctx → Set} → Weakened F [] → F []
unweaken (weakened id t) = t

------------------------------------------------------------------------
-- Normal forms

data Nf : Ctx → Ty → Set
data Ne : Ctx → Ty → Set

data Nf where
  lamₙ : Nf (A ∷ Γ) B → Nf Γ (fun A B)
  lakₙ : Nf Γ B → Nf Γ (fun A B)
  neu  : Ne Γ A → Nf Γ A

data Ne where
  pstₙ : ℕ → (A : Ty) → Ne Γ A
  varₙ : Ne (A ∷ []) A
  appₙ : Cover Γ Γ₁ Γ₂ → Ne Γ₁ (fun A B) → Nf Γ₂ A → Ne Γ B

Weakened-Nf : Ctx → Ty → Set
Weakened-Nf Γ A = Weakened (λ Δ → Nf Δ A) Γ

lakₘ : Weakened-Nf Γ B → Weakened-Nf Γ (fun A B)
lakₘ (weakened δ t) = weakened δ (lakₙ t)

lamₘ : Weakened-Nf (A ∷ Γ) B → Weakened-Nf Γ (fun A B)
lamₘ (weakened id t)             = weakened id (lamₙ t)
lamₘ (weakened  wk t)            = weakened id (lakₙ t)
lamₘ (weakened (ne (keep₁ δ)) t) = weakened (ne δ) (lamₙ t)
lamₘ (weakened (ne (skip₁ δ)) t) = weakened (ne δ) (lakₙ t)

------------------------------------------------------------------------
-- Semantic terms; values

Val  : Ctx → Ty → Set
Val' : Ctx → Ty → Set
Val₁ : Ctx → Ty → Set

Val₁ Γ (bsc _)   = ⊥ -- no introduction terms for postulates
Val₁ Γ (fun A B) = Val' Γ B ⊎ ((Δ Ω : Ctx) → Cover Δ Γ Ω → Val' Ω A → Val Δ B)

Val' Γ A = Ne Γ A ⊎ Val₁ Γ A
Val  Γ A = Weakened (λ Δ → Val' Δ A) Γ

wk-Val : Wk Γ Δ → Val Γ A → Val Δ A
wk-Val = wk-weakened

------------------------------------------------------------------------
-- Evaluation

EvalEnv = Env Val'

lower  : Val  Γ A → Weakened-Nf Γ A
lower' : Val' Γ A → Weakened-Nf Γ A
lower₁ : Val₁ Γ A → Weakened-Nf Γ A

lower₁ {A = bsc _} ()
lower₁ {A = fun A B} (inj₁ t) = lakₘ (lower' t)
lower₁ {A = fun A B} (inj₂ f) = lamₘ (lower (f (A ∷ _) (A ∷ []) (cov₁ inrlⁿ) (inj₁ varₙ)))

lower' (inj₁ t) = weakened id (neu t)
lower' (inj₂ t) = lower₁ t

lower (weakened δ t) = wk-weakened δ (lower' t)

raise : Ne Γ A → Val' Γ A
raise = inj₁

val-lak : Val Γ B → Val Γ (fun A B)
val-lak (weakened δ t) = weakened  δ (inj₂ (inj₁ t))

app-konst' : Cover Γ Γ₁ Γ₂ → Val' Γ₁ A → Val' Γ₂ B → Val Γ A
app-konst' c x _ = weakened (cover-wk₁ c) x

app-konst : Cover Γ Γ₁ Γ₂ → Val Γ₁ A → Val Γ₂ B → Val Γ A
app-konst c x _ = wk-Val (cover-wk₁ c) x

app-val' : Cover Γ Γ₁ Γ₂ → Val' Γ₁ (fun A B) → Val' Γ₂ A → Val Γ B
app-val' c (inj₁ f) t with lower' t
... | weakened δ t' with cover⨟wk₂ c δ
... | _ , c' , δ' = weakened δ' (inj₁ (appₙ c' f t'))
app-val' c (inj₂ (inj₂ f)) t = f _ _ c t
app-val' c (inj₂ (inj₁ f)) t = app-konst' c f t

app-val : Cover Γ Γ₁ Γ₂ → Val Γ₁ (fun A B) → Val Γ₂ A → Val Γ B
app-val c (weakened δ₁ f) (weakened δ₂ t) with cover⨟wk c δ₁ δ₂
... | _ , c' , δ' = wk-Val δ' (app-val' c' f t)

eval' : Tm Γ A → EvalEnv Γ Δ → Val Δ A
eval' (pst x A)   []             = weakened id (raise (pstₙ x A))
eval' (wkn δ t)   env with wk-env δ env
... | _ , δ' , env' = wk-Val δ' (eval' t env')
eval' var         (snoc c [] t)
  with inv-inrⁿ c
... | refl                       = weakened id t
eval' (app c f t) env
  with splitEnv env c
... | _ , _ , c' , env₁ , env₂   = app-val c' (eval' f env₁) (eval' t env₂)
eval' (lam f)     env            = weakened id (inj₂ (inj₂ λ Δ Ω c t → eval' f (snoc c env t)))

eval : EvalEnv Γ Δ → Tm Γ A → Val Δ A
eval env t = eval' t env

normalise-closed' : Tm [] A → Weakened-Nf [] A
normalise-closed' t = lower (eval [] t)

normalise-closed : Tm [] A → Nf [] A
normalise-closed t = unweaken (normalise-closed' t)

private
  _$_ : Tm [] (fun A B) → Tm [] A → Tm [] B
  f $ x = app nil f x
  infixl 0 _$_

_ : normalise-closed (id-Tm {A = A}) ≡ lamₙ (neu varₙ)
_ = refl

_ : normalise-closed (compose-Tm {B = B} $ id-Tm $ id-Tm) ≡ lamₙ (neu varₙ)
_ = refl

_ : normalise-closed (compose-Tm $ const-Tm {B = C} $ const-Tm {A = A} {B = B}) ≡ lamₙ (lakₙ (lakₙ (neu varₙ)))
_ = refl
