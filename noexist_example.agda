----------------
-- Конкретный пример несуществующего алгоритма
----------------

module noexist_example where

open import Agda.Primitive
open import Data.Bool

open import Data.Nat using (ℕ; zero)
open import Data.Nat renaming (suc to sucn; pred to predn)
open import Data.Nat renaming (_+_ to _+n_; _≤_ to _ℕ≤_ ; _<_ to _ℕ<_)
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
open import alg2n
open import noexist

----------------
-- Список и его фильтрованные подсписки
----------------

lis : List (BorderedNlist 3)
lis = p012 ∷ p021 ∷ p120 ∷ p201 ∷ p102 ∷ []

small1 = p012 ∷ p021 ∷ p120 ∷ []

small2 = p012 ∷ p021 ∷ p102 ∷ []

small3 = p012 ∷ p201 ∷ p102 ∷ []

----------------
-- Каждый элемент нашего списка — перестановка
----------------

u102 : (i j : Fin 3) → (i ≢ j) → nth p102 i ≢ nth p102 j
u102 zerof zerof p = ⊥-elim (p refl)
u102 (sucf zerof) (sucf zerof) p = ⊥-elim (p refl)
u102 (sucf (sucf zerof)) (sucf (sucf zerof)) p = ⊥-elim (p refl)
u102 (sucf (sucf (sucf p))) _ _ = ⊥-elim (nolify p)
u102 _ (sucf (sucf (sucf p))) _ = ⊥-elim (nolify p)

u102 zerof (sucf zerof) _ = ncom prf3-01
u102 (sucf zerof) zerof _ = prf3-01

u102 (sucf zerof) (sucf (sucf zerof)) _ = prf3-02
u102 (sucf (sucf zerof)) (sucf zerof) _ = ncom prf3-02

u102 zerof (sucf (sucf zerof)) _ = prf3-12
u102 (sucf (sucf zerof)) zerof _ = ncom prf3-12

--

u201 : (i j : Fin 3) → (i ≢ j) → nth p201 i ≢ nth p201 j
u201 zerof zerof p = ⊥-elim (p refl)
u201 (sucf zerof) (sucf zerof) p = ⊥-elim (p refl)
u201 (sucf (sucf zerof)) (sucf (sucf zerof)) p = ⊥-elim (p refl)
u201 (sucf (sucf (sucf p))) _ _ = ⊥-elim (nolify p)
u201 _ (sucf (sucf (sucf p))) _ = ⊥-elim (nolify p)

u201 zerof (sucf zerof) _ = ncom prf3-02
u201 (sucf zerof) zerof _ = prf3-02

u201 (sucf zerof) (sucf (sucf zerof)) _ = prf3-01
u201 (sucf (sucf zerof)) (sucf zerof) _ = ncom prf3-01

u201 zerof (sucf (sucf zerof)) _ = ncom prf3-12
u201 (sucf (sucf zerof)) zerof _ = prf3-12

--

u120 : (i j : Fin 3) → (i ≢ j) → nth p120 i ≢ nth p120 j
u120 zerof zerof p = ⊥-elim (p refl)
u120 (sucf zerof) (sucf zerof) p = ⊥-elim (p refl)
u120 (sucf (sucf zerof)) (sucf (sucf zerof)) p = ⊥-elim (p refl)
u120 (sucf (sucf (sucf p))) _ _ = ⊥-elim (nolify p)
u120 _ (sucf (sucf (sucf p))) _ = ⊥-elim (nolify p)

u120 zerof (sucf zerof) _ = prf3-12
u120 (sucf zerof) zerof _ = ncom prf3-12

u120 (sucf zerof) (sucf (sucf zerof)) _ = ncom prf3-02
u120 (sucf (sucf zerof)) (sucf zerof) _ = prf3-02

u120 zerof (sucf (sucf zerof)) _ = ncom prf3-01
u120 (sucf (sucf zerof)) zerof _ = prf3-01

--

u021 : (i j : Fin 3) → (i ≢ j) → nth p021 i ≢ nth p021 j
u021 zerof zerof p = ⊥-elim (p refl)
u021 (sucf zerof) (sucf zerof) p = ⊥-elim (p refl)
u021 (sucf (sucf zerof)) (sucf (sucf zerof)) p = ⊥-elim (p refl)
u021 (sucf (sucf (sucf p))) _ _ = ⊥-elim (nolify p)
u021 _ (sucf (sucf (sucf p))) _ = ⊥-elim (nolify p)

u021 zerof (sucf zerof) _ = prf3-02
u021 (sucf zerof) zerof _ = ncom prf3-02

u021 (sucf zerof) (sucf (sucf zerof)) _ = ncom prf3-12
u021 (sucf (sucf zerof)) (sucf zerof) _ = prf3-12

u021 zerof (sucf (sucf zerof)) _ = prf3-01
u021 (sucf (sucf zerof)) zerof _ = ncom prf3-01

--

u012 : (i j : Fin 3) → (i ≢ j) → nth p012 i ≢ nth p012 j
u012 zerof zerof p = ⊥-elim (p refl)
u012 (sucf zerof) (sucf zerof) p = ⊥-elim (p refl)
u012 (sucf (sucf zerof)) (sucf (sucf zerof)) p = ⊥-elim (p refl)
u012 (sucf (sucf (sucf p))) _ _ = ⊥-elim (nolify p)
u012 _ (sucf (sucf (sucf p))) _ = ⊥-elim (nolify p)

u012 zerof (sucf zerof) _ = prf3-01
u012 (sucf zerof) zerof _ = λ p → prf3-01 (eq_comm p)

u012 (sucf zerof) (sucf (sucf zerof)) _ = prf3-12
u012 (sucf (sucf zerof)) (sucf zerof) _ =  λ p → prf3-12 (eq_comm p)

u012 zerof (sucf (sucf zerof)) _ = prf3-02
u012 (sucf (sucf zerof)) zerof _ = λ p → prf3-02 (eq_comm p)

----------------
-- Unicalized для нашего списка
----------------

UNI : Unicalized lis
UNI = u012 u-cons (u021 u-cons (u120 u-cons (u201 u-cons (u102 u-cons u-nil))))

----------------
-- Функция перехода для noexist lis 2
----------------

F : (i j : Fin 3) → (i ≢ j) → (noexist (cmpFilter i j lis) 1 ⊎ noexist (cmpFilter j i lis) 1)
F zerof zerof x = ⊥-elim (x refl)
F (sucf zerof) (sucf zerof) x = ⊥-elim (x refl)
F (sucf (sucf zerof)) (sucf (sucf zerof)) x = ⊥-elim (x refl)

F zerof (sucf zerof) _ = inj₁ (basa small1 1 (s≤s (s≤s (s≤s z≤n))))
F (sucf zerof) zerof _ = inj₂ (basa small1 1 (s≤s (s≤s (s≤s z≤n))))

F zerof (sucf (sucf zerof)) _ = inj₁ (basa small2 1 (s≤s (s≤s (s≤s z≤n))))
F (sucf (sucf zerof)) zerof _ = inj₂ (basa small2 1 (s≤s (s≤s (s≤s z≤n))))

F (sucf zerof) (sucf (sucf zerof)) _ = inj₁ (basa small3 1 (s≤s (s≤s (s≤s z≤n))))
F (sucf (sucf zerof)) (sucf zerof) _ = inj₂ (basa small3 1 (s≤s (s≤s (s≤s z≤n))))

F (sucf (sucf (sucf p))) _ _ = ⊥-elim (nolify p)
F _ (sucf (sucf (sucf p))) _ = ⊥-elim (nolify p)

----------------
-- Не существует алгоритма глубины 2,
-- сортирующего список lis
----------------

noexistprf : noexist lis 2
noexistprf = pereh lis 1 F

noalgprf : (a : Alg lis) → (depth a ℕ≤ 2) → ⊥
noalgprf = noexistNoAlg (s≤s (s≤s z≤n)) UNI noexistprf
