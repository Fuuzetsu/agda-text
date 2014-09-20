module Data.Text.Properties where

     import Algebra.FunctionProperties
     import Data.Vec                        as V
     import Relation.Binary.EqReasoning
open import Data.Char                               hiding (setoid)
open import Data.List                       as List hiding (length)
open import Data.Maybe                              hiding (setoid)
open import Data.Nat
open import Data.Nat.Properties.Simple
open import Data.Product
open import Data.String                             hiding (setoid)
open import Data.Text
open import Data.Text.Array
open import Function
open import Relation.Binary.PropositionalEquality

module StringHelpers where
  str-len : String → ℕ
  str-len = List.length ∘ Data.String.toList

open StringHelpers

open ≡-Reasoning
open Text

-- Consing a character makes the text larger by one.
cons+1 : ∀ {c} {t : Text} → length (cons c t) ≡ suc (length t)
cons+1 = refl

cons>0 : ∀ c (t : Text) → 0 < length (cons c t)
cons>0 _ _ = s≤s z≤n

snoc+1 : ∀ {c} (t : Text) → length (snoc t c) ≡ suc (length t)
snoc+1 _ = refl

snoc>0 : ∀ c (t : Text) → 0 < length (snoc t c)
snoc>0 _ _ = s≤s z≤n

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

append-empty : (t : Text) → append t empty ≡ t
append-empty (text V.[]) = refl
append-empty (text (x V.∷ x₁)) =
   cong (append (singleton x)) (append-empty (text x₁))

append-empty-l : (t : Text) → append empty t ≡ t
append-empty-l (text x) = refl

applen : (t : Text) → length (append t empty) ≡ length t
applen = cong length ∘ append-empty

append-l : {t t' : Text} → length t + length t' ≡ length (append t t')
append-l = refl

-- unconsing empty always gives nothing
uncons-empty : {t : Text} → {p : 0 ≡ length t} → uncons t ≡ nothing
uncons-empty {text V.[]} {refl} = refl

-- unconsing non-empty always gives just
uncons-nempty : {t : Text} {p : 0 < length t}
              → uncons t ≡ just (head t {p} , tail t {p})
uncons-nempty {text (x V.∷ x₁)} {s≤s p} = refl

-- cons followed by head = id
head-cons : ∀ {c} {t : Text} → head (cons c t) {cons>0 c t} ≡ c
head-cons = refl

-- cons preserves last
last-cons : ∀ {c} (t : Text) {p : 0 < length t}
          → last (cons c t) {cons>0 c t} ≡ last t {p}
last-cons (text (x V.∷ x₁)) {s≤s z≤n} = refl

-- snoc preserves last
last-snoc : ∀ {c} → (t : Text) → last (snoc t c) {snoc>0 c t} ≡ c
last-snoc (text V.[]) = refl
last-snoc {c} (text {suc n} (x V.∷ x₁)) = begin
  last (cons x (snoc t c)) ≡⟨ last-cons (snoc t c) {p = snoc>0 c t } ⟩
  last (snoc (text x₁) c) ≡⟨ last-snoc (text x₁) ⟩
  c ∎
  where
    t = text x₁

-- tail ∘ cons c is identity
cons-tail : ∀ {c} {t : Text} → tail (cons c t) {cons>0 c t} ≡ t
cons-tail {t = text x} = refl

{-
-- Between n Texts ‘ts’, we insert ‘t’ n - 1 times so the length ends
-- up being ‘length t * (n - 1) + sum (map length ts)’ where n =
-- List.length ts
intercalate-len : (t : Text) (ts : List Text)
                → length (intercalate t ts)
                   ≡ (length t * (List.length ts ∸ 1))
                     + sum (List.map length ts)
intercalate-len t [] = begin
  0 ≡⟨ sym (*-right-zero (length t)) ⟩
  length t * 0 ≡⟨ sym $ +-right-identity (length t * 0) ⟩
  length t * 0 + 0 ∎
intercalate-len t (x ∷ ts) = begin
  lx + length (intercalate-go t ts)
  ≡⟨ sym {!!}  ⟩
  lx + sum ls + lt * lts
  ≡⟨ +-comm (lx + sum ls) (lt * lts) ⟩
  lt * lts + (length x + sum ls)
  ∎
  where
    lt = length t
    lts = List.length ts
    ls = List.map length ts
    lx = length x

    intercal-one : (t t' : Text)
                 → length (intercalate t List.[ t' ]) ≡ length t'
    intercal-one t (text t') = cong length (append-empty (text t'))

    -- la : (t t' : Text) → length t + length t' ≡ length (append t t')
-}

-- init ∘ flip snoc c is identity
-- snoc-init : ∀ {c} (t : Text) → init (snoc t c) {snoc>0 c t} ≡ t
-- snoc-init (text V.[]) = refl
-- snoc-init {c} (text (x V.∷ xs)) with snoc (text xs) c
-- snoc-init (text (x V.∷ xs)) | text body = cong text {!!}

-- snoc-init (text (x V.∷ .V.[])) | V.[] , .x , refl | refl = refl
-- snoc-init (text (x V.∷ .(proj₁ V.∷ʳ proj₂))) | .x V.∷ proj₁ , proj₂ , refl | b =

-- snoc-init c (text (x V.∷ .V.[])) | V.[] , .x , refl = refl
-- snoc-init c (text (x V.∷ .(proj₁ V.∷ʳ lastc))) | .x V.∷ proj₁ , lastc , refl =
--   cong text p
--   where
--     p : {!!}
--     p = {!!}
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
