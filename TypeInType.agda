module TypeInType where

-- IAL:
open import eq
open import level
open import negation
open import product

data Tree (ℓ : level) : Set (lsuc ℓ) where
  Sup : (a : Set ℓ) → (f : a → Tree ℓ) → Tree ℓ

A : ∀ {ℓ} → Tree ℓ → Set ℓ
A (Sup a _) = a

F : ∀ {ℓ} → (t : Tree ℓ) → A t → Tree ℓ
F (Sup _ f) = f

Normal : ∀ {ℓ} → Tree ℓ → Set (lsuc ℓ)
Normal t = ¬ (Σ (A t) (λ y → F t y ≡ Sup (A t) (F t)))

NT : ∀ {ℓ} → Set (lsuc ℓ)
NT {ℓ} = Σ (Tree ℓ) (λ t → Normal t)

P : ∀ {ℓ} → NT → Tree ℓ
P (x , _) = x

R : ∀ {ℓ} → Tree ℓ
R = Sup NT P

{- Agda objects to the use of P in the last line above:

(Set .ℓ) != (Set (lsuc .ℓ))
when checking that the expression P has type NT → Tree .ℓ -}

