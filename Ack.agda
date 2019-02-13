module Ack where

open import nat    -- from IAL

ack : ℕ → ℕ → ℕ
ack zero n = suc n
ack (suc m) zero = ack m 1
ack (suc m) (suc n) = ack m (ack (suc m) n)
