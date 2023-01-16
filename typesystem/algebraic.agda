-- A typesystem and CPS interpreter for algebraic effects and handlers
-- (deep and shallow)

module algebraic where

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Bool using (true; false; if_then_else_) renaming (Bool to 𝔹)
open import Data.String using (String)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality
open Relation.Binary.PropositionalEquality.≡-Reasoning


-- Types
data Ty : Set

data Tr : Set

data Mc : Set

data H  : Set

data Ty where
  Nat  : Ty
  Bool : Ty
  Str  : Ty
  _⇒_⟨_,_⟩_⟨_,_⟩_ : Ty → Ty → Tr → Mc → Ty → Tr → Mc → Ty → Ty

data Tr where
  ● : Tr
  _⇨⟨_,_⟩_ : Ty → Tr → Mc → Ty → Tr

infix 5 _⇨⟨_,_⟩_

data Mc where
  [] : Mc
  _⇨⟨_,_⟩_×_×_::_ : Ty → Tr → Mc → Ty → Tr → H → Mc → Mc

infix 7 _⇨⟨_,_⟩_×_×_::_

data H where
  _⇒_⇒_⟨_,_⟩_⟨_,_⟩_ : Ty → Ty → Ty → Tr → Mc → Ty → Tr → Mc → Ty → H

infix 6 _⇒_⇒_⟨_,_⟩_⟨_,_⟩_


-- cons and append of trail
compatible : Tr → Tr → Tr → Set
compatible ● μ₂ μ₃ = μ₂ ≡ μ₃
compatible (τ₁ ⇨⟨ μ₁ , σ₁ ⟩ τ₁') ● μ₃ = (τ₁ ⇨⟨ μ₁ , σ₁ ⟩ τ₁') ≡ μ₃
compatible (τ₁ ⇨⟨ μ₁ , σ₁ ⟩ τ₁') (τ₂ ⇨⟨ μ₂ , σ₂ ⟩ τ₂') ● = ⊥
compatible (τ₁ ⇨⟨ μ₁ , σ₁ ⟩ τ₁') (τ₂ ⇨⟨ μ₂ , σ₂ ⟩ τ₂')
           (τ₃ ⇨⟨ μ₃ , σ₃ ⟩ τ₃') =
             (τ₁ ≡ τ₃) × (compatible (τ₂ ⇨⟨ μ₂ , σ₂ ⟩ τ₂') μ₃ μ₁) ×
             (σ₁ ≡ σ₃) × (τ₁' ≡ τ₃')


-- initial continuation
id-cont-type : Ty → Tr → Mc → Ty → Set
id-cont-type τ ● [] τ' = τ ≡ τ'
id-cont-type τ ● (τ₁ ⇨⟨ μ₁ , σ₁ ⟩ τ₂ × μ₂ × η :: σ₂) τ' =
               (τ ≡ τ₁) × (μ₁ ≡ μ₂) × (σ₁ ≡ σ₂) × (τ' ≡ τ₂)
id-cont-type τ (τ₁ ⇨⟨ μ₁ , σ₁ ⟩ τ₁') σ τ' =
               (τ ≡ τ₁) × (μ₁ ≡ ●) × (σ ≡ σ₁) × (τ' ≡ τ₁')


-- the following variables automatically become implicit arguments
variable
  τ τ' τ₀ τ₀' τ₁ τ₂ τ₃ τ₄ τ₅ τv τvc α β γ γ' δ : Ty
  μ μ' μ₀ μ₀' μ₁ μ₂ μ₂' μ₃ μ₄ μα μβ μγ μid : Tr
  σ σ' σ₀ σ₀' σ₁ σ₂ σ₃ σ₄ σα σβ σγ σid : Mc
  η : H


-- Terms
-- e : Exp var τ μα σα α μβ σβ β  means that e
--  * has type τ
--  * requires
--      - a context that yields a computation of type α
--        when given a trail of type μα and a metacontext of type σα
--      - a trail of type μβ
--      - a metacontext of type σβ
--  * eventually returns a value of type β
data Exp (var : Ty → Set) : Ty → Tr → Mc → Ty → Tr → Mc → Ty → Set where
  Var         : var τ → Exp var τ μα σα α μα σα α
  Num         : ℕ → Exp var Nat μα σα α μα σα α
  Bol         : 𝔹 → Exp var Bool μα σα α μα σα α
  Lam         :   (var τ₂ → Exp var τ₁ μβ σβ β μγ σγ γ)
                → Exp var (τ₂ ⇒ τ₁ ⟨ μβ , σβ ⟩ β ⟨ μγ , σγ ⟩ γ)
                      μα σα α μα σα α
  App         :   Exp var (τ₂ ⇒ τ₁ ⟨ μα , σα ⟩ α ⟨ μ₂ , σ₂ ⟩ β)
                      μ₁ σ₁ γ μβ σβ δ
                → Exp var τ₂ μ₂ σ₂ β μ₁ σ₁ γ
                → Exp var τ₁ μα σα α μβ σβ δ
  Plus        :   Exp var Nat μγ σγ γ μβ σβ β
                → Exp var Nat μα σα α μγ σγ γ
                → Exp var Nat μα σα α μβ σβ β
  If          :   Exp var Bool μγ σγ γ μβ σβ δ
                → Exp var α μα σα β μγ σγ γ
                → Exp var α μα σα β μγ σγ γ
                → Exp var α μα σα β μβ σβ δ
  Is0         :   Exp var Nat μα σα α μβ σβ β
                → Exp var Bool μα σα α μβ σβ β
  B2S         :   Exp var Bool μα σα α μβ σβ β
                → Exp var Str μα σα α μβ σβ β
  TryWith     :   id-cont-type γ μid σid γ'
                → Exp var γ μid σid γ' ●
                      (τ ⇨⟨ μα , σα ⟩ α × μβ ×
                      (τ' ⇒ τvc ⇒ τ₃ ⟨ μ₃ , σ₃ ⟩ τ₄ ⟨ μ₄ , σ₄ ⟩ τ₅)
                        :: σβ)
                      β
                → (var τ' → var τvc → Exp var τ₃ μ₃ σ₃ τ₄ μ₄ σ₄ τ₅)
                → Exp var τ μα σα α μβ σβ β
  CallDeep    :   Exp var τ' μα
                      (τ₀ ⇨⟨ μ₀ , σ₀ ⟩ τ₀' × μ₀' ×
                       (τ' ⇒ (τ ⇒ τ₁ ⟨ μ₁ , σ₁ ⟩ τ₂ ⟨ μ₂ , σ₂ ⟩ α) ⇒
                        τ₀ ⟨ μ₀ , σ₀ ⟩ τ₀' ⟨ μ₀' , σ₀' ⟩ γ) :: σ₀')
                      γ μβ σβ β
                → Exp var τ μα
                      (τ₁ ⇨⟨ μ₁ , σ₁ ⟩ τ₂ × μ₂ ×
                       (τ' ⇒ (τ ⇒ τ₁ ⟨ μ₁ , σ₁ ⟩ τ₂ ⟨ μ₂ , σ₂ ⟩ α) ⇒
                        τ₀ ⟨ μ₀ , σ₀ ⟩ τ₀' ⟨ μ₀' , σ₀' ⟩ γ) :: σ₂)
                      α μβ σβ β
  CallShallow :   compatible (τ₁ ⇨⟨ μ₁ , σ₁ ⟩ τ₂) μ₂ μ₂'
                → compatible μ' μ₂' μα
                → Exp var τ' μ'
                      (τ₀ ⇨⟨ μ₀ , σ₀ ⟩ τ₀' × μ₀' ×
                       (τ' ⇒ (τ ⇒ τ₁ ⟨ μ₁ , σ₁ ⟩ τ₂ ⟨ μ₂ , σα ⟩ α) ⇒
                        τ₀ ⟨ μ₀ , σ₀ ⟩ τ₀' ⟨ μ₀' , σ₀' ⟩ γ) :: σ₀')
                      γ μβ σβ β
                → Exp var τ μα σα α μβ σβ β
            


-- Interpretation of types
〚_〛τ : Ty → Set
〚_〛μ : Tr → Set
〚_〛σ : Mc → Set
〚_〛η : H  → Set


--- Ty
〚 Nat 〛τ = ℕ
〚 Bool 〛τ = 𝔹
〚 Str 〛τ = String
〚 τ₁ ⇒ τ₂ ⟨ μα , σα ⟩ α ⟨ μβ , σβ ⟩ β 〛τ =
  〚 τ₁ 〛τ → (〚 τ₂ 〛τ → 〚 μα 〛μ → 〚 σα 〛σ → 〚 α 〛τ) →
  〚 μβ 〛μ → 〚 σβ 〛σ → 〚 β 〛τ

--- Tr
〚 ● 〛μ = ⊤
〚 τ₁ ⇨⟨ μ , σ ⟩ τ₂ 〛μ = 〚 τ₁ 〛τ → 〚 μ 〛μ → 〚 σ 〛σ → 〚 τ₂ 〛τ

--- Mc
〚 [] 〛σ = ⊤
〚 τ ⇨⟨ μ , σ ⟩ τ' × μ' × η :: σ' 〛σ =
  ((〚 τ 〛τ → 〚 μ 〛μ → 〚 σ 〛σ → 〚 τ' 〛τ) × 〚 μ' 〛μ × 〚 η 〛η)
  × 〚 σ' 〛σ

--- H
〚 τv ⇒ τvc ⇒ τ ⟨ μα , σα ⟩ α ⟨ μβ , σβ ⟩ β 〛η =
  〚 τv 〛τ → 〚 τvc 〛τ → (〚 τ 〛τ → 〚 μα 〛μ → 〚 σα 〛σ → 〚 α 〛τ) →
  〚 μβ 〛μ → 〚 σβ 〛σ → 〚 β 〛τ


-- compose trail
compose-trail : compatible μ₁ μ₂ μ₃ → 〚 μ₁ 〛μ → 〚 μ₂ 〛μ → 〚 μ₃ 〛μ
compose-trail {●} refl tt t₂ = t₂
compose-trail {τ₁ ⇨⟨ μ₁ , σ₁ ⟩ τ₁'} {●} refl t₁ tt = t₁
compose-trail {τ₁ ⇨⟨ μ₁ , σ₁ ⟩ τ₁'} {τ₂ ⇨⟨ μ₂ , σ₂ ⟩ τ₂'}
              {τ₃ ⇨⟨ μ₃ , σ₃ ⟩ τ₃'} (refl , c , refl , refl) t₁ t₂ =
                λ v t m → t₁ v (compose-trail c t₂ t) m


-- initial continaution
idc : id-cont-type τ μ σ τ' → 〚 τ 〛τ → 〚 μ 〛μ → 〚 σ 〛σ → 〚 τ' 〛τ
idc {μ = ●} {[]} refl v tt tt = v
idc {μ = ●} {τ₁ ⇨⟨ μ₁ , σ₁ ⟩ τ₂ × .μ₁ × η :: .σ₁}
    (refl , refl , refl , refl) v tt ((c , t , h) , m) = c v t m
idc {μ = τ ⇨⟨ .● , σ ⟩ τ'} (refl , refl , refl , refl) v c m = c v tt m


-- if b then (g e₂ env c t₁ m₁) else (g e₃ env c t₁ m₁)
if-then-else : 𝔹 → 〚 γ 〛τ → 〚 γ 〛τ → 〚 γ 〛τ
if-then-else true v₂ v₃ = v₂
if-then-else false v₂ v₃ = v₃


-- is0
is0 : ℕ → 𝔹
is0 zero = true
is0 (suc _) = false


-- b2s
b2s : 𝔹 → String
b2s true = "true"
b2s false = "false"


-- CPS interpreter
g : {var : Ty → Set} → Exp 〚_〛τ τ μα σα α μβ σβ β →
    (〚 τ 〛τ → 〚 μα 〛μ → 〚 σα 〛σ → 〚 α 〛τ) →
    〚 μβ 〛μ → 〚 σβ 〛σ → 〚 β 〛τ
g (Var x) c t m = c x t m
g (Num n) c t m = c n t m
g (Bol b) c t m = c b t m
g (Lam f) c t m = c (λ v c₁ t₁ m₁ → g {var = 〚_〛τ} (f v) c₁ t₁ m₁) t m
g (App e₁ e₂) c t m =
  g {var = 〚_〛τ} e₁
    (λ v₁ t₁ m₁ → g {var = 〚_〛τ} e₂ (λ v₂ t₂ m₂ → v₁ v₂ c t₂ m₂) t₁ m₁) t m
g (Plus e₁ e₂) c t m =
  g {var = 〚_〛τ} e₁
    (λ n₁ t₁ m₁ →
      g {var = 〚_〛τ} e₂ (λ n₂ t₂ m₂ → c (n₁ + n₂) t₂ m₂) t₁ m₁) t m
g (If e₁ e₂ e₃) c t m =
  g {var = 〚_〛τ} e₁
    (λ b t₁ m₁ → 
     if-then-else b (g {var = 〚_〛τ} e₂ c t₁ m₁) (g {var = 〚_〛τ} e₃ c t₁ m₁))
    t m 
g (Is0 e) c t m = g {var = 〚_〛τ} e (λ n t₁ m₁ → c (is0 n) t₁ m₁) t m
g (B2S e) c t m = g {var = 〚_〛τ} e (λ b t₁ m₁ → c (b2s b) t₁ m₁) t m
g (TryWith id-c-t e₁ e₂) c t m =
  g {var = 〚_〛τ} e₁ (idc id-c-t) tt
    ((c , t , λ v vc c₁ t₁ m₁ → g {var = 〚_〛τ} (e₂ v vc) c₁ t₁ m₁) , m) 

g (CallDeep e) c t m =
  g {var = 〚_〛τ} e
    (λ { v t₁ ((c₀ , t₀ , h) , m₀) →
           h v (λ v₂ c₂ t₂ m₂ → c v₂ t₁ ((c₂ , t₂ , h) , m₂)) c₀ t₀ m₀})
    t m

g (CallShallow ct₁ ct₂ e) c t m =
  g {var = 〚_〛τ} e
    (λ { v t₁ ((c₀ , t₀ , h) , m₀) →
           h v (λ v₂ c₂ t₂ m₂ →
                     c v₂ (compose-trail ct₂ t₁ (compose-trail ct₁ c₂ t₂)) m₂)
             c₀ t₀ m₀})
    t m


-- Top-level evaluation
f : Exp 〚_〛τ τ ● [] τ ● [] τ → 〚 τ 〛τ
f e = g {var = 〚_〛τ} e (λ v _ _ → v) tt tt
