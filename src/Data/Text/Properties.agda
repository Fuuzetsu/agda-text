module Data.Text.Properties where

open import Relation.Binary.PropositionalEquality
import Relation.Binary.EqReasoning
open import Data.Text
import Data.Vec as V
open import Data.Nat
open import Data.Text.Array
open import Data.String
open import Data.List as List hiding (length)
open import Function
open import Data.Product
open import Data.Maybe
open import Data.Char
import Algebra.FunctionProperties

module StringHelpers where
  str-len : String → ℕ
  str-len = List.length ∘ Data.String.toList

open StringHelpers

open ≡-Reasoning

-- Consing a character makes the text larger by one.
cons+1 : ∀ {c} {t : Text} → length (cons c t) ≡ suc (length t)
cons+1 {t = text (array x)} = refl

cons>0 : ∀ {c} {t : Text} → 0 < length (cons c t)
cons>0 {t = text (array x)} = s≤s z≤n

snoc+1 : ∀ {c} {t : Text} → length (snoc t c) ≡ suc (length t)
snoc+1 {t = text (array V.[])} = refl
snoc+1 {c} {t = text (array {suc n} (x V.∷ x₁))} = begin
  length (cons x (snoc t c))
  ≡⟨ cons+1 {t = snoc t c} ⟩
  suc (length (snoc t c))
  ≡⟨ cong suc (snoc+1 {t = text (array x₁)}) ⟩
  suc (suc n)
  ∎
  where
    t = text (array x₁)

snoc>0 : ∀ {c} {t : Text} → 0 < length (snoc t c)
snoc>0 {t = text (array V.[])} = s≤s z≤n
snoc>0 {c} {text (array (x V.∷ x₁))} = cons>0 {t = snoc (text (array x₁)) c}

snoc-empty : ∀ {c} → length (cons c empty) ≡ 1
snoc-empty = refl

-- Consing to an empty text is one character
cons-empty : ∀ {c} → length (cons c empty) ≡ 1
cons-empty = refl

empty-len : length empty ≡ 0
empty-len = refl

-- Packing preserves length
pack-l : {s : String} → str-len s ≡ length (pack s)
pack-l = refl


-- unconsing empty always gives nothing
uncons-empty : {t : Text} → {p : 0 ≡ length t} → uncons t ≡ nothing
uncons-empty {text (array V.[])} {refl} = refl

-- unconsing non-empty always gives just
uncons-nempty : {t : Text} {p : 0 < length t}
              → uncons t ≡ just (head t {p} , tail t {p})
uncons-nempty {text (array (x V.∷ x₁))} {s≤s p} = refl

-- cons followed by head = id
head-cons : ∀ {c} {t : Text} → head (cons c t) {cons>0 {t = t}} ≡ c
head-cons {t = text (array x)} = refl

-- cons preserves last
last-cons : ∀ {c} {t : Text} {p : 0 < length t}
          → last (cons c t) {cons>0 {t = t}} ≡ last t {p}
last-cons {t = text (array (x V.∷ x₁))} {s≤s z≤n} = refl

-- snoc preserves last
last-snoc : ∀ {c} → {t : Text} → last (snoc t c) {snoc>0 {t = t}} ≡ c
last-snoc {t = text (array V.[])} = refl
last-snoc {c} {t = text (array {suc n} (x V.∷ x₁))} = begin
  last (cons x (snoc t c))
  ≡⟨ last-cons {t = snoc t c} {p = snoc>0 {t = t}} ⟩
  last (snoc (text (array x₁)) c)
  ≡⟨ last-snoc {t = text (array x₁)} ⟩
  c
  ∎
  where
    t = text (array x₁)

-- tail ∘ cons c is identity
cons-tail : ∀ {c} {t : Text} → tail (cons c t) {cons>0 {t = t}} ≡ t
cons-tail {t = text (array x)} = refl

-- init ∘ flip snoc c is identity
{-
snoc-init : ∀ {c} {t : Text} → init (snoc t c) {snoc>0 {t = t}} ≡ t
snoc-init {t = text (array V.[])} = refl
snoc-init {c} {t = text (array {suc n} (x V.∷ x₁))} = begin
  init (snoc t' c) {cons>0 {t = snoc t c}}
  ≡⟨ {!!} ⟩
  t'
  ∎
  where
    t = text (array x₁)
    t' = text (array (x V.∷ x₁))
-}

{- TODO:
reverse (reverse t) ≡ t
init (snoc t c) ≡ t
-}
