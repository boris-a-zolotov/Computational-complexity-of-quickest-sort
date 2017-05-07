----------------
-- Определение перестановки;
-- сравнение её элементов, filter
----------------

module permutation_definition where

open import Agda.Primitive
open import Data.Bool
open import IO.Primitive using (IO; putStrLn)
open import Foreign.Haskell using (Unit)

open import Data.Nat using (ℕ; _+_; _∸_; suc; pred; zero)
open import Data.Nat.Base using (_*_; _<_; _≤_; _≰_) 
open import Data.Nat.Base public using (z≤n; s≤s)
open import Data.Nat.Properties using (m≢1+m+n; m≤m+n)

open import Data.Fin renaming (compare to cmpFin)
open import Data.Fin renaming (zero to zerof; suc to sucf; inject₁ to inj)
open import Data.Fin renaming (_<_ to _lessThan_; _≤_ to _lessEq_)

open import Data.List using (List; []; _++_)
open import Data.List.Base using (_∷_)
open import Relation.Binary.Core public using (_≡_; refl; _≢_)
open import Relation.Nullary.Negation

----------------
-- Ограниченный список данной длины
----------------

data Nlist (A : Set) : ℕ → Set where
  «» : Nlist A 0
  _—_ : {n : ℕ} → A → Nlist A n → Nlist A (suc n)

BorderedNlist : ℕ → Set
BorderedNlist n = Nlist (Fin n) n

nth : {m : ℕ} {n : ℕ} → Nlist (Fin n) m → Fin n → Fin n
nth {_} {0} _ ()
nth {0} {suc n} «» _ = zerof
nth {suc m} {suc n} (x — y) zerof = x
nth {suc m} {suc n} (x — y) (sucf t) = nth {m} {suc n} y (inj t)

----------------
-- Сравнение и фильтр в списке перестановок
----------------

filter : ∀ {M : Set} → (M → Bool) → List M → List M
filter p [] = []
filter p (x ∷ ls) with p x
... | true = x ∷ (filter p ls)
... | false = filter p ls

isLess : {n : ℕ} → {a b : Fin n} → Ordering a b → Bool
isLess (less _ _) = true
isLess _ = false

numCmp : {n : ℕ} → (a b : Fin n) → Bool
numCmp {n} a b = isLess {n} {a} {b} (cmpFin a b)

listCmp : {n : ℕ} → (i j : Fin n) → (l : BorderedNlist n) → Bool
listCmp {n} i j l = numCmp {n} (nth l i) (nth l j)

cmpFilter : {n : ℕ} → (i j : Fin n) → (l : List (BorderedNlist n)) → List (BorderedNlist n)
cmpFilter {n} i j l = filter (listCmp {n} i j) l
