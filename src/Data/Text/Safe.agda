-- This is an implementation of text functionality which can be
-- considered statically safer. The downside is that it does not
-- reflect the Haskell interface closely but the hope for this module
-- is to use it in Data.Text, turning these static, internal proofs
-- into Haskell interface + external proofs.
--
-- This should hopefully result in cleaner implementation than trying
-- to implement the Haskell way straight away and then to reason about
-- it.
module Data.Text.Safe where

import Data.List as L
import Data.Product as P
import Data.Vec as V
open import Data.Char using (Char; toNat)
open import Data.Nat
open import Data.String as S
open import Function
open import Relation.Binary.PropositionalEquality

record Text (n : ℕ) (v : V.Vec Char n) : Set where

vec→text : ∀ {n} → (v : V.Vec Char n) → Text n v
vec→text = _

text→vec : ∀ {n v} → Text n v → V.Vec Char n
text→vec {v = v} _ = v

length : ∀ {n v} → Text n v → ℕ
length {n} _ = n

pack : (s : S.String) → Text _ (toVec s)
pack = _

unpack : ∀ {n v} → Text n v → String
unpack {v = v} _ = S.fromList (V.toList v)

singleton : (c : Char) → Text _ V.[ c ]
singleton = _

empty : Text _ V.[]
empty = _

cons : ∀ {n v} → (c : Char) → Text n v → Text _ (c V.∷ v)
cons = _

snoc : ∀ {n v} → Text n v → (c : Char) → Text _ (v V.∷ʳ c)
snoc = _

append : ∀ {n m v v₁} → Text n v → Text m v₁ → Text _ (v V.++ v₁)
append = _

head : ∀ {n v} → Text (suc n) v → Char
head {v = v} _ = V.head v

last : ∀ {n v} → Text (suc n) v → Char
last {v = v} _ = V.last v

tail : ∀ {n v} → Text (suc n) v → Text _ (V.tail v)
tail = _

-- Get out a char and a proof that the char was in the vector
uncons : ∀ {n v} → Text (suc n) v
       → (P.Σ Char (λ c → c ≡ V.head v)) P.× Text _ (V.tail v)
uncons {v = v} _ = (V.head v P., refl) P., _

init : ∀ {n v} → Text (suc n) v → Text _ (V.init v)
init = _

compareLength : ∀ {n v} → Text n v → (m : ℕ) → Ordering n m
compareLength {n = n} _ = compare n

map : ∀ {n v} → (f : Char → Char) → Text n v → Text n (V.map f v)
map = _

-- Insert an element between every element in the vector. This
-- effectivelly inserts an element before every element in the
-- vector's tail, resulting in n - 1 new elements, so n + n - 1,
-- 2 * n - 1
intersperseVec : ∀ {n ℓ} {A : Set ℓ} (a : A) → V.Vec A n
               → V.Vec A (n * 2 ∸ 1)
intersperseVec a V.[] = V.[]
intersperseVec {A = A} a (x V.∷ v) = x V.∷ go v
  where
    go : ∀ {n} → V.Vec A n → V.Vec A (n * 2)
    go V.[] = V.[]
    go (x₁ V.∷ v₁) = a V.∷ x₁ V.∷ go v₁

intersperse : ∀ {n v} (c : Char) → (t : Text n v) → Text _ (intersperseVec c v)
intersperse = _

reverse : ∀ {n v} → Text n v → Text n (V.reverse v)
reverse = _

replicateVec : ∀ {n ℓ} {A : Set ℓ} (m : ℕ) → V.Vec A n
             → V.Vec A (m * n)
replicateVec zero v = V.[]
replicateVec (suc m) v = v V.++ replicateVec m v

replicate : ∀ {n v} (m : ℕ) → Text n v → Text (m * n) (replicateVec m v)
replicate = _

replicateChar : (n : ℕ) → (c : Char) → Text n (V.replicate c)
replicateChar = _

justifyLeft : ∀ {n v} → (m : ℕ) → (c : Char) → Text n v
            → Text (n + (m ∸ n)) (v V.++ V.replicate {n = m ∸ n} c)
justifyLeft = _

justifyRight : ∀ {n v} → (m : ℕ) → (c : Char) → Text n v
             → Text (m ∸ n + n) (V.replicate {n = m ∸ n} c V.++ v)
justifyRight = _

foldl : ∀ {n v ℓ} {A : Set ℓ} → (A → Char → A) → A → Text n v → A
foldl {v = v} {A = A} f s _ = V.foldl (const A) f s v

foldl1 : ∀ {n v} → (Char → Char → Char) → Text (suc n) v → Char
foldl1 {v = x V.∷ _} f = foldl f x

foldr : ∀ {n v ℓ} {A : Set ℓ} → (Char → A → A) → A → Text n v → A
foldr {v = v} {A = A} f s _ = V.foldr (const A) f s v

foldr1 : ∀ {n v ℓ} {A : Set ℓ} → (Char → Char → Char) → Text (suc n) v → Char
foldr1 {v = x V.∷ _} f = foldr f x

take : (m : ℕ) → ∀ {n v} → Text (m + n) v → Text m (V.take m v)
take = _

takeEnd : (m : ℕ) → ∀ {n v} → Text (m + n) v → Text m (V.take m (V.reverse v))
takeEnd = _

drop : (m : ℕ) → ∀ {n v} → Text (m + n) v → Text n (V.drop m v)
drop = _

dropEnd : (m : ℕ) → ∀ {n v} → Text (m + n) v → Text n (V.drop m (V.reverse v))
dropEnd = _

Text* : ℕ → Set
Text* = V.Vec (P.∃₂ Text)

unrollVec : ∀ {n} → (v : Text* n)
          → V.Vec _ (V.sum (V.map P.proj₁ v))
unrollVec V.[] = V.[]
unrollVec (x V.∷ x₁) = P.proj₁ (P.proj₂ x) V.++ unrollVec x₁

concat : ∀ {n} → (x : Text* n) → Text _ _
concat = vec→text ∘ unrollVec

concatMap : ∀ {n v} → (f : _ → P.∃₂ Text) → Text n v → Text _ _
concatMap {v = v} f _ = concat (V.map f v)

splitAt : (m : ℕ) → ∀ {n v} → Text (m + n) v
        → Text m (P.proj₁ (V.splitAt m v))
           P.× Text n (P.proj₁ (P.proj₂ (V.splitAt m v)))
splitAt = _

len : ∀ {n ℓ} {A : Set ℓ} → V.Vec A n → ℕ
len {n} _ = n

vec : (v : P.∃₂ Text) → V.Vec Char (len (P.proj₁ (P.proj₂ v)))
vec (proj₁ P., proj₂ P., proj₃) = proj₂

-- Prefix each inner vector with the given one
intercalate-go : ∀ {n m v}
               → (t : Text n v)
               → (tl : Text* m)
               → V.Vec (P.∃₂ (λ o → Text (n + o))) m
intercalate-go t = V.map (λ x → _ P., _ P., append t (P.proj₂ (P.proj₂ x)))


headVec : ∀ {m} → (t : Text* (suc m)) → V.Vec Char (len (vec (V.head t)))
headVec ((proj₁ P., proj₂ P., proj₃) V.∷ xs) = proj₂

-- intercalate : ∀ {n v m} → (t : Text n v) (tl : Text* m)
--             → Text (((len tl ∸ 1) * len v) + length (concat tl)) {!!}
-- intercalate _ V.[] = empty
-- intercalate t (v V.∷ vs) = append (P.proj₂ (P.proj₂ v)) (concat (intercalate-go {!t!} vs))

-- intersperseVec : ∀ {n ℓ} {A : Set ℓ} (a : A) → V.Vec A n → V.Vec A (n * 2 ∸ 1)

-- intercalate : ∀ {n v m} → (t : Text n v) (tl : Text* m)
--             → Text _ _
-- intercalate {v = v} = {!!}

-- What a nasty thing.
data Any {ℓ} (P : Char → Set ℓ) : ∀ {n v} → Text n v → Set ℓ where
  here : ∀ {c n} {cs : V.Vec Char n} {t : Text n cs} → P c → Any P (cons c t)
  there : ∀ {n} {c : Char} {cs : V.Vec Char n} {t : Text n cs}
        → Any P t → Any P (cons c t)

module Membership {ℓ} (P : Char → Set ℓ) where
  _∈_ : ∀ {n v} → Char → Text n v → Set ℓ
  c ∈ t = Any P t

  open import Relation.Nullary

  _∉_ : ∀ {n v} → Char → Text n v → Set ℓ
  c ∉ t = ¬ c ∈ t

  _⊆_ : ∀ {n v m v₁} → Text n v → Text m v₁ → Set ℓ
  t ⊆ t₁ = ∀ {c} → c ∈ t → c ∈ t₁

  _⊈_ : ∀ {n v m v₁} → Text n v → Text m v₁ → Set ℓ
  t ⊈ t₁ = ¬ t ⊆ t₁

  ∉empty : ∀ {b} → b ∉ empty
  ∉empty ()
