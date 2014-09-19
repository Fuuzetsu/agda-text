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

module StringHelpers where
  str-len : String → ℕ
  str-len = List.length ∘ Data.String.toList

open StringHelpers

snoc+1 : ∀ {c n} {t : Text {n}} → length (snoc t c) ≡ suc n
snoc+1 {t = text (array x)} = refl

snoc-empty : ∀ {c} → length (cons c empty) ≡ 1
snoc-empty = refl

-- Consing a character makes the text larger by one.
cons+1 : ∀ {c n} {t : Text {n}}  → length (cons c t) ≡ suc n
cons+1 {t = text (array x)} = refl

-- Consing to an empty text is one character
cons-empty : ∀ {c} → length (cons c empty) ≡ 1
cons-empty = refl

empty-len : length empty ≡ 0
empty-len = refl

-- Packing preserves length
pack-l : {s : String} → str-len s ≡ length (pack s)
pack-l = refl

uncons-empty : {t : Text {0}} → uncons t ≡ nothing
uncons-empty {text (array V.[])} = refl

uncons-nempty : ∀ {n} {t : Text {suc n}} → uncons t ≡ just (head t , tail t)
uncons-nempty {t = text (array (x V.∷ x₁))} = refl

head-cons : ∀ {c n} {t : Text {n}} → head (cons c t) ≡ c
head-cons {t = text (array x)} = refl

last-snoc : ∀ {c n} {t : Text {n}} → last (snoc t c) ≡ c
last-snoc {t = text (array V.[])} = refl
last-snoc {c} {n = suc n} {text (array .{suc n} (x V.∷ x₁))} =
  let v = text (array x₁) in trans (ign (snoc v c)) (last-snoc { t = v })
  where
    ign : ∀ {d m} → (t' : Text {suc m}) → last (cons d t') ≡ last t'
    ign (text (array (x₂ V.∷ x₃))) = refl

cons-tail : ∀ {c n} {t : Text {n}} → tail (cons c t) ≡ t
cons-tail {t = text (array x)} = refl

open ≡-Reasoning
open import Data.Empty

-- end my suffering
-- snoc-init : ∀ {c n} {t : Text {n}} → init (snoc t c) ≡ t
