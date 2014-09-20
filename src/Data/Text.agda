-- Implementation of the interface given by the ‘text’ Haskell
-- package. Notably, this does not prove ‘text’ correct, it just aims
-- to give the same results with none of the performance or
-- implementation.
module Data.Text where


open import Data.Char
open import Data.Fin as F using ()
open import Data.List as List using (List)
open import Data.Maybe as Maybe using (Maybe)
open import Data.Nat
open import Data.Product using (_,_; _×_)
open import Data.String
open import Data.Text.Array
open import Data.Vec as V using (toList; []; _∷_; _∷ʳ_)
open import Function
open import Relation.Binary.PropositionalEquality

record Text : Set where
  constructor text
  field
    {length} : ℕ
    body : V.Vec Char length

open Text

untext : (t : Text) → V.Vec Char (length t)
untext (text x) = x

data IText : ℕ → Set where
  itext : (t : Text) → IText (length t)

itext′ : ∀ {n} → IText n → Text
itext′ (itext t) = t

liftV : ∀ {m n} → (V.Vec Char m → V.Vec Char n) → IText m → IText n
liftV f (itext (text x)) = itext (text (f x))

appV : ∀ {ℓ} {A : Set ℓ} (t : Text) (f : IText (length t) → A) → A
appV t f = f (itext t)

pack : (s : String) → Text
pack = text ∘ toVec

unpack : Text → String
unpack (text x) = fromList (V.toList x)

singleton : Char → Text
singleton c = text (c ∷ [])

empty : Text
empty = text V.[]

cons : Char → Text → Text
cons c t = itext′ (consi c (itext t))
  where
    consi : ∀ {m} → Char → IText m → IText (suc m)
    consi c₁ (itext (text x)) = itext (text (c₁ ∷ x))

snoc : Text → Char → Text
snoc t c = itext′ $ snoci (itext t) c
  where
    snoci : ∀ {m} → IText m → Char → IText (suc m)
    snoci (itext (text x)) c′ = itext (text (x V.∷ʳ c′))

append : Text → Text → Text
append (text x) t' = itext′ (liftV (V._++_ x) (itext t'))

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
init (text x) {s≤s p} = text x

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

replicateChar : ℕ → Char → Text
replicateChar n c = replicate n (singleton c)

justifyLeft : ℕ → Char → Text → Text
justifyLeft n c t = append t (replicateChar (n ∸ length t) c)

justifyRight : ℕ → Char → Text → Text
justifyRight n c t = append (replicateChar (n ∸ length t) c) t

foldl : ∀ {ℓ} {A : Set ℓ} → (A → Char → A) → A → Text → A
foldl {A = A} f s = V.foldl (const A) f s ∘ untext

foldl1 : (Char → Char → Char) → (t : Text) {p : 0 < length t} → Char
foldl1 f (text (x ∷ x₁)) {s≤s p} = V.foldl (const Char) f x x₁

foldr : ∀ {ℓ} {A : Set ℓ} → (Char → A → A) → A → Text → A
foldr {A = A} f s = V.foldr (const A) f s ∘ untext

foldr1 : (Char → Char → Char) → (t : Text) {p : 0 < length t} → Char
foldr1 f (text (x ∷ body)) {s≤s _} = V.foldr (const Char) f x body

concat : List Text → Text
concat = List.foldl append empty

concatMap : (Char → Text) → Text → Text
concatMap f = concat ∘ V.toList ∘ V.map f ∘ untext

any : (Char → Bool) → Text → Bool
any p (text []) = false
any p (text (x ∷ body)) with p x
... | true = true
... | false = any p (text body)

all : (Char → Bool) → Text → Bool
all p (text []) = true
all p (text (x ∷ body)) with p x
... | true = all p (text body)
... | false = false

take : ℕ → Text → Text
take (suc n) (text (x ∷ body)) = cons x (take n (text body))
take _ t = empty

drop : ℕ → Text → Text
drop (suc n) (text (x ∷ body)) = drop n (text body)
drop _ t = t

{- stopped at Substrings today -}

{- TODO:
* transpose
* replace
* case folds (?)
* center
* maximum/minimum
* Construction
-}
