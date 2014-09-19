-- Implementation of the interface given by the ‘text’ Haskell
-- package. Notably, this does not prove ‘text’ correct, it just aims
-- to give the same results with none of the performance or
-- implementation.
module Data.Text where

open import Data.Char
open import Data.List as List using (List)
open import Data.Maybe as Maybe using (Maybe)
open import Data.Nat renaming (compare to compareℕ)
open import Data.Product using (_,_; _×_)
open import Data.String
open import Data.Text.Array
open import Data.Vec as V using (toList; []; _∷_; _∷ʳ_)
open import Function

data Text {n : ℕ} : Set where
  text : Array n → Text

pack : (s : String) → Text
pack = text ∘ array ∘ toVec

unpack : ∀ {n} → Text {n} → String
unpack (text (array x)) = fromList (V.toList x)

singleton : Char → Text {1}
singleton c = text (array ( c ∷ []))

empty : Text {0}
empty = text (array V.[])

cons : ∀ {n} → Char → Text {n} → Text {1 + n}
cons c (text (array x)) = text (array (c ∷ x))

snoc : ∀ {n} → Text {n} → Char → Text {1 + n}
snoc (text (array [])) c = text (array V.[ c ])
snoc (text (array (x ∷ x₁))) c = cons x (snoc (text (array x₁)) c)

append : ∀ {n m} → Text {n} → Text {m} → Text {n + m}
append (text (array x)) (text (array x₁)) = text (array (x V.++ x₁))

uncons : ∀ {n} → Text {n} → Maybe (Char × Text {pred n})
uncons (text (array [])) = Maybe.nothing
uncons (text (array (x ∷ x₁))) = Maybe.just (x , text (array x₁))

head : ∀ {n} → Text {suc n} → Char
head (text (array (x ∷ x₁))) = x

last : ∀ {n} → Text {suc n} → Char
last (text (array (x ∷ []))) = x
last {suc n} (text (array (x ∷ x₁))) = last (text (array x₁))

tail : ∀ {n} → Text {suc n} → Text {n}
tail (text (array (x ∷ x₁))) = text (array x₁)

init : ∀ {n} → Text {suc n} → Text {n}
init (text (array x)) = text (array (V.init x))


open import Data.Bool as B
null : ∀ {n} → Text {n} → B.Bool
null (text (array [])) = B.true
null (text (array (x ∷ x₁))) = B.false

length : ∀ {n} → Text {n} → ℕ
length {n} _ = n

compareLength : ∀ {n} → Text {n} → (m : ℕ) → Ordering n m
compareLength t m = compareℕ (length t) m

map : ∀ {n} → (Char → Char) → Text {n} → Text {n}
map f (text (array x)) = text (array (V.map f x))

-- _+⋎_ : ℕ → ℕ → ℕ
-- zero  +⋎ n = n
-- suc m +⋎ n = suc (n +⋎ m)

-- Ugly addition ;_;
intersperse : ∀ {n} → Char → Text {n} → Text {n +⋎ pred n}
intersperse c (text (array [])) = text (array [])
intersperse c (text (array (x ∷ xs))) = text (array (x ∷ go xs))
  where
    go : ∀ {m} → V.Vec Char m → V.Vec Char (m +⋎ m)
    go [] = []
    go {suc m} (y ∷ ys) = c ∷ y ∷ go ys

reverse : ∀ {n} → Text {n} → Text {n}
reverse (text (array x)) = text (array (V.reverse x))


open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

subst' : ∀ {ℓ ℓ₁} {A : Set ℓ} {P : {_ : A} → Set ℓ₁} → {x y : A}
       → x ≡ y → P {x} → P {y}
subst' refl x₁ = x₁

-- | subst' specialised to Text
st : ∀ {n m} → n ≡ m → Text {n} → Text {m}
st = subst'

open import Data.Nat.Properties.Simple
replicate : ∀ {n} → (m : ℕ) → Text {n} → Text {m * n}
replicate zero t = empty
replicate {n} (suc zero) t = st (sym $ +-right-identity n) t
replicate (suc m) t = append t (replicate m t)

justifyLeft : ∀ {n} → (m : ℕ) → Char → Text {n} → Text {m ⊔ n}
justifyLeft {n} zero c t = t
justifyLeft {zero} m c t = st p (replicate m (singleton c))
  where
    l : ∀ m → m * 1 ≡ m
    l zero = refl
    l (suc m) = cong suc (l m)

    l' : ∀ m → m ⊔ zero ≡ m
    l' = λ { zero → refl; (suc m) → refl }

    p : m * 1 ≡ m ⊔ zero
    p = trans (l m) (sym $ l' m)

justifyLeft (suc m) c (text (array (x ∷ x₁))) =
  cons x (justifyLeft m c (text (array x₁)))


{- TODO:
* intercalate
* transpose
* replace
* case folds (?)
-}
