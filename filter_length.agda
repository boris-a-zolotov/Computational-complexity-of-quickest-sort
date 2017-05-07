----------------
-- Куча свойств, которые непременно пригодятся
----------------

----------------
-- 1. Свойства следующего числа
-- 2. Cвязь равенства числа и следующего за ним
-- 3. Перенос равенств и неравенств с натуральных чисел на конечные
-- 4. Правда и ложь
-- 5. Свойства длины списка
-- 6. Голова и длина фильтруемого списка
-- 7. Построение Ордеринга по обычному сравнению
-- 8. Преобразование всегда возвращает less
-- 9. Дихотомия строгого неравенства натуральных чисел
----------------

module filter_length where

open import Agda.Primitive
open import Data.Bool
open import IO.Primitive using (IO; putStrLn)
open import Foreign.Haskell using (Unit)

open import Data.Nat using (ℕ; _∸_; zero)
open import Data.Nat renaming (suc to sucn; pred to predn)
open import Data.Nat renaming (_+_ to _+n_)
open import Data.Nat.Base using (_*_; _<_; _≤_; _≰_) 
open import Data.Nat.Base public using (z≤n; s≤s)
open import Data.Nat.Properties using (m≢1+m+n; m≤m+n)
open import Data.Nat.Properties.Simple using (+-comm)

open import Data.Fin renaming (compare to cmpFin)
open import Data.Fin renaming (zero to zerof; suc to sucf; inject₁ to inj)
open import Data.Fin renaming (_<_ to _lessThan_)

open import Data.List using (List; []; _++_)
open import Data.List.Base using (_∷_; filter)
open import Relation.Binary.Core public using (_≡_; refl; _≢_)
open import Relation.Nullary.Negation

open import Data.Empty
open import Data.Sum

open import permutation_definition
open import equation_properties

----------------
-- 1. Свойства следующего числа
----------------

suc+x : ∀ m n → suc (m +n n) ≡ (suc m) +n n
suc+x _ _ = refl

x+suc : ∀ m n → suc (m +n n)≡ m +n (suc n) 
x+suc m n =  eq_trans {ℕ} {suc (m +n n)} {suc (n +n m)} {m +n (suc n)}
  (eq_cong (suc) (+-comm m n))
  (eq_trans {ℕ} {suc (n +n m)} {suc n +n m} {m +n suc n} (suc+x n m) (+-comm (suc n) m))

predsuc : (n : ℕ) → n ≡ predn (sucn n)
predsuc 0 = refl
predsuc (sucn y) = refl

----------------
-- 2. Cвязь равенства числа и следующего за ним
----------------

suceq : {n : ℕ} → (x y : Fin n) → x ≡ y → suc x ≡ suc y
suceq {n} x y p = eq_cong {Fin n} {Fin (suc n)} {x} {y} suc p 

predneq : {n : ℕ} → (x y : Fin n) → (suc x ≢ suc y) → (x ≢ y)
predneq x y = contraposition {_} {_} {x ≡ y} {suc x ≡ suc y} (suceq x y)

----------------
-- 3. Перенос равенств и неравенств с натуральных чисел на конечные
----------------

toℕineq : {a : ℕ} → (m n : Fin a) → m lessThan n → (toℕ m) Data.Nat.< (toℕ n)
toℕineq _ zero ()
toℕineq zero (suc y) _ = s≤s z≤n
toℕineq (suc x) (suc y) (s≤s p) = s≤s (toℕineq x y p)

finnoteq : {a : ℕ} → (m n : Fin a) → m lessThan n → m ≡ n → ⊥
finnoteq zero zero ()
finnoteq (suc x) zero ()
finnoteq zero (suc x) p ()
finnoteq {suc a} (suc x) (suc y) p q = contradiction
  (eq_cong toℕ q)
  (noteq (toℕ (suc x)) (toℕ (suc y)) (toℕineq (suc x) (suc y) p))

----------------
-- 4. Правда и ложь
----------------

falsetrue : (false ≡ true) → ⊥
falsetrue ()

f-to-t : ∀ {x} → x ≡ false → x ≡ true → ⊥
f-to-t {x} p q = falsetrue (eq_trans (eq_comm p) q)

t-to-f : ∀ {x} → (x ≡ true → ⊥) → x ≡ false
t-to-f {x} p with x
... | true = contradiction refl p
... | false = refl

----------------
-- 5. Свойства длины списка
----------------

length : ∀ {a} {A : Set a} → (l : List A) → ℕ
length [] = 0
length (x ∷ l) = sucn (length l)

suclength : {n : ℕ} → (x : BorderedNlist n) → ∀ l → length (x ∷ l) ≡ sucn (length l)
suclength _ [] = refl
suclength _ (x ∷ ls) = refl

predlength : {n : ℕ} → (x : BorderedNlist n) → ∀ l → length l ≡ predn (length (x ∷ l))
predlength _ l = predsuc (length l)

----------------
-- 6. Голова и длина фильтруемого списка
----------------

addHead : ∀ {n} → ∀ i j → ∀ x → ∀ ls →
  listCmp {n} i j x ≡ true →
  cmpFilter i j (x ∷ ls) ≡ x ∷ (cmpFilter i j ls)
addHead {n} i j x ls p with (listCmp i j x)
... | false = ⊥-elim (falsetrue p)
... | true = refl

dropHead : ∀ {n} → ∀ i j → ∀ x → ∀ ls →
  listCmp {n} i j x ≡ false →
  cmpFilter i j (x ∷ ls) ≡ cmpFilter i j ls
dropHead {n} i j x ls p with (listCmp i j x)
... | true = ⊥-elim (falsetrue (eq_comm p))
... | false = refl

addLength : ∀ {n} → ∀ i j → ∀ x → ∀ ls →
  listCmp {n} i j x ≡ true →
  length (cmpFilter i j (x ∷ ls)) ≡ sucn (length (cmpFilter i j ls))

addLength i j x ls p = eq_trans {ℕ}
  {length (cmpFilter i j (x ∷ ls))}
  {length (x ∷ (cmpFilter i j ls))}
  {sucn (length (cmpFilter i j ls))}
  (eq_cong length (addHead i j x ls p))
  (suclength x (cmpFilter i j ls))

dropLength : ∀ {n} → ∀ i j → ∀ x → ∀ ls →
  listCmp {n} i j x ≡ false →
  length (cmpFilter i j (x ∷ ls)) ≡ length (cmpFilter i j ls)

dropLength i j x ls p = eq_cong length (dropHead i j x ls p)

----------------
-- 7. Построение Ордеринга по обычному сравнению
----------------

incLess : ∀ {n} → {i j : Fin n} → Data.Fin.Ordering i j → Data.Fin.Ordering (suc i) (suc j)
incLess (less m n) = less (suc m) (suc n)
incLess (equal m) = equal (suc m)
incLess (greater m n) = greater (suc m) (suc n)

lessToLess : ∀ {n} → (i j : Fin n) → (p : i Data.Fin.< j) → Data.Fin.Ordering i j
lessToLess _ zero ()
lessToLess zero (suc x) p = less (suc x) zero
lessToLess (suc y) (suc x) (s≤s p) = incLess (lessToLess y x p)

----------------
-- 8. Преобразование всегда возвращает less
----------------

IncIsLess : {n : ℕ} → {a b : Fin n} → (p : Data.Fin.Ordering a b) → isLess p ≡ true → isLess (incLess p) ≡ true
IncIsLess (greater m n) ()
IncIsLess (equal m) ()
IncIsLess (less m n) p = refl

lessAlwaysLess : {n : ℕ} → (x y : Fin n) → (p : x lessThan y) →
  (isLess (lessToLess x y p) ≡ false) → ⊥
lessAlwaysLess _ zero ()
lessAlwaysLess zero (suc y) p q =
  falsetrue (eq_trans {Bool}
    {false} {isLess (lessToLess zero (suc y) p)} {true}
    (eq_comm q) refl)
lessAlwaysLess (suc x) (suc y) (s≤s p) q = lessAlwaysLess x y p
  (t-to-f ((contraposition (λ P → IncIsLess (lessToLess x y p) P))
    (f-to-t q)))

----------------
-- 9. Дихотомия строгого неравенства натуральных чисел
----------------

raiseOneStep : {n : ℕ} → (a b c d : Fin n) → (a lessThan b) ⊎ (c lessThan d) →
  ((suc a) lessThan (suc b)) ⊎ ((suc c) lessThan (suc d))
raiseOneStep a b c d (inj₁ p) = inj₁ (s≤s p)
raiseOneStep a b c d (inj₂ q) = inj₂ (s≤s q)

oneOfInequiv : {n : ℕ} → (i j : Fin n) → (i ≢ j) → (i lessThan j) ⊎ (j lessThan i)
oneOfInequiv zero zero p = ⊥-elim (p refl)
oneOfInequiv zero (suc x) _ = inj₁ (s≤s z≤n)
oneOfInequiv (suc x) zero _ = inj₂ (s≤s z≤n)
oneOfInequiv (suc x) (suc y) p = raiseOneStep x y y x (oneOfInequiv x y (predneq x y p))
