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
  text : ∀ {n} → Array n → Text


length : Text → ℕ
length (text (array {n} x)) = n

pack : (s : String) → Text
pack = text ∘ array ∘ toVec

unpack : Text → String
unpack (text (array x)) = fromList (V.toList x)

singleton : Char → Text
singleton c = text (array ( c ∷ []))

empty : Text
empty = text (array V.[])

cons : Char → Text → Text
cons c (text (array x)) = text (array (c ∷ x))

snoc : Text → Char → Text
snoc (text (array [])) c = text (array V.[ c ])
snoc (text (array (x ∷ x₁))) c = cons x (snoc (text (array x₁)) c)

append : Text → Text → Text
append (text (array x)) (text (array x₁)) = text (array (x V.++ x₁))

uncons : Text → Maybe (Char × Text)
uncons (text (array [])) = Maybe.nothing
uncons (text (array (x ∷ x₁))) = Maybe.just (x , text (array x₁))

head : (t : Text) → {p : 0 < length t} → Char
head (text (array [])) {()}
head (text (array (x ∷ x₁))) {s≤s x₂} = x

last : (t : Text) → {p : 0 < length t} → Char
last (text (array [])) {()}
last (text (array (x ∷ []))) {s≤s p} = x
last (text (array (x ∷ x₁ ∷ x₂))) {s≤s p} =
  last (text (array (x₁ ∷ x₂))) {s≤s z≤n}


tail : (t : Text) → {p : 0 < length t} → Text
tail (text (array [])) {()}
tail (text (array (x ∷ x₁))) {s≤s p} = text (array x₁)

init : (t : Text) → {p : 0 < length t} → Text
init (text (array [])) {()}
init (text (array x)) {s≤s p} = text (array (V.init x))


open import Data.Bool as B
null : Text → B.Bool
null (text (array [])) = B.true
null (text (array (x ∷ x₁))) = B.false

compareLength : (t : Text)→ (m : ℕ) → Ordering (length t) m
compareLength t m = compare (length t) m


map : (Char → Char) → Text → Text
map f (text (array x)) = text (array (V.map f x))

-- Ugly addition ;_;
intersperse : Char → Text → Text
intersperse c (text (array [])) = text (array [])
intersperse c (text (array (x ∷ xs))) = text (array (x ∷ go xs))
  where
    go : ∀ {m} → V.Vec Char m → V.Vec Char (m +⋎ m)
    go [] = []
    go {suc m} (y ∷ ys) = c ∷ y ∷ go ys


reverse : Text → Text
reverse (text (array x)) = text (array (V.reverse x))

replicate : ℕ → Text → Text
replicate zero t = empty
replicate (suc zero) t = t
replicate (suc m) t = append t (replicate m t)

justifyLeft : ℕ → Char → Text → Text
justifyLeft zero c t = empty
justifyLeft (suc m) c (text (array {zero} [])) =
  replicate (suc m) (singleton c)
justifyLeft (suc m) c (text (array {suc n} (x ∷ x₁))) =
  cons x (justifyLeft m c (text (array x₁)))


open ≡-Reasoning

{- TODO:
* intercalate
* transpose
* replace
* case folds (?)
-}
