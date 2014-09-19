-- Implementation of the interface given by the ‘text’ Haskell
-- package. Notably, this does not prove ‘text’ correct, it just aims
-- to give the same results with none of the performance or
-- implementation.
module Data.Text where

open import Data.Char
open import Data.List as List using (List)
open import Data.Maybe as Maybe using (Maybe)
open import Data.Nat
open import Data.Product using (_,_; _×_)
open import Data.String
open import Data.Text.Array
open import Data.Vec as V using (toList; []; _∷_; _∷ʳ_)
open import Function
open import Relation.Binary.PropositionalEquality

data Text : Set where
  text : ∀ {n} → V.Vec Char n → Text

length : Text → ℕ
length (text {n} x) = n

pack : (s : String) → Text
pack = text ∘ toVec

unpack : Text → String
unpack (text x) = fromList (V.toList x)

singleton : Char → Text
singleton c = text (c ∷ [])

empty : Text
empty = text V.[]

cons : Char → Text → Text
cons c (text x) = text (c ∷ x)

snoc : Text → Char → Text
snoc (text []) c = text V.[ c ]
snoc (text (x ∷ x₁)) c = cons x (snoc (text x₁) c)

append : Text → Text → Text
append (text x) (text x₁) = text (x V.++ x₁)

uncons : Text → Maybe (Char × Text)
uncons (text []) = Maybe.nothing
uncons (text (x ∷ x₁)) = Maybe.just (x , text x₁)

head : (t : Text) → {p : 0 < length t} → Char
head (text []) {()}
head (text (x ∷ x₁)) {s≤s x₂} = x

last : (t : Text) → {p : 0 < length t} → Char
last (text []) {()}
last (text (x ∷ [])) {s≤s p} = x
last (text (x ∷ x₁ ∷ x₂)) {s≤s p} =
  last (text (x₁ ∷ x₂)) {s≤s z≤n}


tail : (t : Text) → {p : 0 < length t} → Text
tail (text []) {()}
tail (text (x ∷ x₁)) {s≤s p} = text x₁

init : (t : Text) → {p : 0 < length t} → Text
init (text []) {()}
init (text x) {s≤s p} = text (V.init x)


open import Data.Bool as B
null : Text → B.Bool
null (text []) = B.true
null (text (x ∷ x₁)) = B.false

compareLength : (t : Text)→ (m : ℕ) → Ordering (length t) m
compareLength t m = compare (length t) m

map : (Char → Char) → Text → Text
map f (text x) = text (V.map f x)

intercalate-go : Text → List Text → Text
intercalate-go _ List.[] = empty
intercalate-go t (y List.∷ ys) = append (append t y) (intercalate-go t ys)

intercalate : Text → List Text → Text
intercalate t List.[] = empty
intercalate t (x List.∷ ts) = append x (intercalate-go t ts)

-- Ugly addition ;_;
intersperse : Char → Text → Text
intersperse c (text []) = text []
intersperse c (text (x ∷ xs)) = text (x ∷ go xs)
  where
    go : ∀ {m} → V.Vec Char m → V.Vec Char (m +⋎ m)
    go [] = []
    go {suc m} (y ∷ ys) = c ∷ y ∷ go ys


reverse : Text → Text
reverse (text x) = text (V.reverse x)

replicate : ℕ → Text → Text
replicate zero t = empty
replicate (suc zero) t = t
replicate (suc m) t = append t (replicate m t)

justifyLeft : ℕ → Char → Text → Text
justifyLeft zero c t = empty
justifyLeft (suc m) c (text []) = replicate (suc m) (singleton c)
justifyLeft (suc m) c (text (x ∷ x₁)) = cons x (justifyLeft m c (text x₁))


open ≡-Reasoning

{- TODO:
* intercalate
* transpose
* replace
* case folds (?)
-}
