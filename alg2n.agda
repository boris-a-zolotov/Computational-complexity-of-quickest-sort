----------------
-- Длина обслуживаемого списка
----------------

module alg2n where

open import Agda.Primitive
open import Data.Bool

open import Data.Nat using (ℕ; _∸_; zero)
open import Data.Nat renaming (suc to sucn; pred to predn)
open import Data.Nat renaming (_+_ to _+n_; _≤_ to _ℕ≤_ )
open import Data.Nat.Base using (_*_; z≤n; s≤s) 
open import Data.Nat.Properties using (m≤m+n; m≤m⊔n)
open import Data.Nat.Properties using (_+-mono_; pred-mono)
open import Data.Nat.Properties.Simple using (+-*-suc; *-comm; +-comm)
open import Data.Nat.Properties.Simple using (+-right-identity; *-right-zero)

open import Data.Fin renaming (compare to cmpFin)
open import Data.Fin renaming (zero to zerof; suc to sucf; inject₁ to inj)
open import Data.Fin renaming (_<_ to _lessThan_)

open import Data.List using (List; []; _++_)
open import Data.List.Base using (_∷_; filter)
open import Relation.Binary.Core public using (_≡_; refl; _≢_)
open import Relation.Nullary.Negation

open import Data.Empty
open import Data.Sum

open import equation_properties
open import permutation_definition
open import algorithm
open import filter_length
open import final_length

----------------
-- Плюс 1 в степени двойки — два одинаковых слагаемых
----------------

*1=+0 : (n : ℕ) → n * 1 ≡ n +n 0
*1=+0 (n) = eq_trans {ℕ} {n * 1} {n +n n * 0} {n +n 0}
  (+-*-suc n 0)
  (eq_cong {ℕ} {ℕ} {n * 0} {0} (λ x → n +n x) (*-right-zero n))

*1=id : (n : ℕ) → n * 1 ≡ n
*1=id (n) = eq_trans {ℕ} {n * 1} {n +n 0} {n} (*1=+0 n) (+-right-identity n)

+n*1=+n : (n : ℕ) → n +n n * 1 ≡ n +n n
+n*1=+n (n) = eq_cong {ℕ} {ℕ} {n * 1} {n} (λ x -> n +n x) (*1=id n)

*2=sum : (n : ℕ) →  n * 2 ≡ n +n n
*2=sum (n) = eq_trans {ℕ} {n * 2} {n +n n * 1} {n +n n}
  (+-*-suc n 1) (+n*1=+n n)

PlusIsInc : {n : ℕ} → 2 ^ (suc n) ≡ 2 ^ n +n 2 ^ n
PlusIsInc {n} = eq_trans {ℕ} {2 ^ (suc n)} {(2 ^ n) * 2} {2 ^ n +n 2 ^ n}
  (refl) (*2=sum (2 ^ n))

PlusIsIncComm : {n : ℕ} → 2 ^ n +n 2 ^ n ≡ 2 ^ (suc n)
PlusIsIncComm {n} = eq_comm (PlusIsInc {n})

----------------
-- Неравенства для степеней
----------------

nextdeg : (n : ℕ) → 2 ^ (n) ℕ≤ 2 ^ (suc n)
nextdeg n = trans_≤_eq
  (m≤m+n (2 ^ n) (2 ^ n))
  (PlusIsIncComm {n})

degs_ineq : {m n : ℕ} → (m ℕ≤ n) → (2 ^ m ℕ≤ 2 ^ n)
degs_ineq {0} {0} p = s≤s p
degs_ineq {0} {suc l} p = trans_≤ (degs_ineq {0} {l} (z≤n)) (nextdeg l)
degs_ineq {suc k} {suc l} p =
   trans_difficult {2 ^ (suc k)} {2 ^ k +n 2 ^ k} {2 ^ l +n 2 ^ l} {2 ^ (suc l)}
  (PlusIsInc {k})
  (preserv (degs_ineq {k} {l} (pred-mono p)) (degs_ineq {k} {l} (pred-mono p)))
  (PlusIsIncComm {l})
degs_ineq {suc q} {0} ()

----------------
-- Определение подсписка.
-- Подсписок инъективен.
-- Фильтр является подсписком.
----------------

data _⊆_ {A : Set} : List A → List A → Set where
  stop : [] ⊆ []
  drop : ∀ {x ls l} → ls ⊆ l → ls ⊆ (x ∷ l)
  keep : ∀ {x ls l} → ls ⊆ l → (x ∷ ls) ⊆ (x ∷ l)

projUnic : {n : ℕ} → {ls l : List (BorderedNlist n)} →
  Unicalized l → ls ⊆ l → Unicalized ls
projUnic u-nil stop = u-nil
projUnic (f u-cons u) (keep p) = f u-cons (projUnic u p)
projUnic (f u-cons u) (drop p) = projUnic u p

filterIn : {n : ℕ} → (i j : Fin n) → (l : List (BorderedNlist n)) →
  cmpFilter i j l ⊆ l
filterIn i j [] = stop
filterIn i j (x ∷ ls) with (listCmp i j x)
... | true = keep (filterIn i j ls)
... | false = drop (filterIn i j ls)

filterUnic : {n : ℕ} → (i j : Fin n) → (l : List (BorderedNlist n)) →
  Unicalized l → Unicalized (cmpFilter i j l)
filterUnic i j l u = projUnic u (filterIn i j l)

----------------
-- Функции на алгоритмах
----------------

depth : {n : ℕ} → {l : List (BorderedNlist n)} → Alg l → ℕ
depth (leaf b) = 0
depth (node i j p a1 a2) = suc ((depth a1) ⊔⊔ (depth a2))

leafnum : {n : ℕ} → {l : List (BorderedNlist n)} → Alg l → ℕ
leafnum (leaf b) = 1
leafnum (node i j p a1 a2) = (leafnum a1) +n (leafnum a2)

toList : {n : ℕ} → {l : List (BorderedNlist n)} → Alg l
  → List (BorderedNlist n)
toList {n} {l} a = l

----------------
-- Длина обслуживаемого списка
-- не превосходит количества листьев
----------------

lenLeafNum : {n : ℕ} → {l : List (BorderedNlist n)} →
  (a : Alg l) → Unicalized l → (length l ℕ≤ leafnum a)

lenLeafNum (leaf b) _ = me≤ 1 1 refl
lenLeafNum (node i j pn a1 a2) u =
  let a = node i j pn a1 a2 in
    trans_≤
    {length (toList a)}
    {length (cmpFilter i j (toList a)) +n length (cmpFilter j i (toList a))}
    {leafnum a1 +n leafnum a2}
    (FILTERLENGTH i j pn (toList a) u)
    (preserv (lenLeafNum a1 (filterUnic i j (toList a) u)) (lenLeafNum a2 (filterUnic j i (toList a) u)))

----------------
-- Количество листьев в алгоритме
----------------

lmmaxsum : (x y : ℕ) → 2 ^ x +n 2 ^ y ℕ≤ 2 ^ (x ⊔⊔ y) +n 2 ^ (x ⊔⊔ y)
lmmaxsum x y = preserv (degs_ineq (m≤m⊔n x y)) (degs_ineq (n≤m⊔n x y))

lmmax2 : (x y : ℕ) → 2 ^ x +n 2 ^ y ℕ≤ 2 ^ (suc (x ⊔⊔ y))
lmmax2 x y = trans_≤_eq {2 ^ x +n 2 ^ y} {2 ^ (x ⊔⊔ y) +n 2 ^ (x ⊔⊔ y)} {2 ^ (suc (x ⊔⊔ y))} (lmmaxsum x y) (PlusIsIncComm {x ⊔⊔ y})

alg2n : {n : ℕ} → {l : List (BorderedNlist n)} → (a : Alg l) → (leafnum a ℕ≤ 2 ^ (depth a))
alg2n (leaf b) = ≤-refl
alg2n (node i j p a1 a2) = trans_≤
  {leafnum a1 +n leafnum a2}
  {2 ^ depth a1 +n 2 ^ depth a2}
  {2 ^ (suc (depth a1 ⊔⊔ depth a2))}
  (preserv (alg2n a1) (alg2n a2))
  (lmmax2 (depth a1) (depth a2))

----------------
-- Основное неравенство: обслужим
-- не более 2^depth перестановок
----------------

len2depth : {n : ℕ} → {l : List (BorderedNlist n)} → (a : Alg l) →
  Unicalized l → (length l  ℕ≤  2 ^ (depth a))
len2depth a u = trans_≤ (lenLeafNum a u) (alg2n a)
