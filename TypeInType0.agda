module TypeInType0 where

-- IAL:
open import eq
open import level
open import negation
open import product

data Tree : Set lone where
  Sup : (a : Set) → (f : a → Tree) → Tree

A : Tree → Set
A (Sup a _) = a

F : (t : Tree) → A t → Tree
F (Sup _ f) = f

Normal : Tree → Set lone
Normal t = ¬ (Σ (A t) (λ y → F t y ≡ Sup (A t) (F t)))

NT : Set lone
NT = Σ Tree (λ t → Normal t)

P : NT → Tree
P (x , _) = x

R : Tree
R = Sup NT P

{- Agda objects to the use of NT in the last line above:

Set₁ != Set
when checking that the expression NT has type Set

-}
