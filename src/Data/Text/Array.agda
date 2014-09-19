module Data.Text.Array where

open import Data.Vec
open import Data.Char
open import Data.Nat

data Array : ℕ → Set where
  array : {n : ℕ} → Vec Char n → Array n

aLen : ∀ {n} → Array n → ℕ
aLen {n} _ = n
