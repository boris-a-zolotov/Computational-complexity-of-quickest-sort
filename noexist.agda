----------------
-- Доказательство несуществования
-- алгоритмов. Noexist.
----------------

----------------
-- 1. Определение noexist
-- 2. Ослабление неравенств
-- 3. Технические утверждения
-- 4. Фильтрованный список короче оригинального
-- 5. Глубина сыновей алгоритма невелика
-- 6. Бредим, если сортируем 1 элемент
-- 7. Не сортируется — длины хотя бы 2
-- 8. Понижение невозможной глубины
-- 9. Отсутствие алгоритма из-за noexist
----------------

module noexist where

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

----------------
-- 1. Определение noexist
----------------

data noexist : {n : ℕ} → (l : List (BorderedNlist n)) → (depth : ℕ) → Set where
  basa : {n : ℕ} → (l : List (BorderedNlist n)) → (d : ℕ) → (2 ^ d ℕ< length l) → noexist l d
  pereh : {n : ℕ} → (l : List (BorderedNlist n)) → (d : ℕ) →
    ((i j : Fin n) → (i ≢ j) → (noexist (cmpFilter i j l) d ⊎ noexist (cmpFilter j i l) d)) →
    noexist l (suc d)

----------------
-- 2. Ослабление неравенств
----------------

decrease≤ : {m n : ℕ} → (suc m) ℕ≤ (suc n) → m ℕ≤ n
decrease≤ (s≤s p) = p

next≤ : {m n : ℕ} → m ℕ< n → m ℕ≤ n
next≤ (s≤s z≤n) = z≤n
next≤ {suc m} {suc n} (s≤s p) = s≤s (next≤ {m} {n} p)

stepup : (n : ℕ) → n ℕ≤ suc n
stepup 0 = z≤n
stepup (sucn m) = s≤s (stepup m)

1≤deg : (n : ℕ) → 1 ℕ≤ 2 ^ n
1≤deg n = degs_ineq {0} {n} z≤n

----------------
-- 3. Технические утверждения
----------------

prfn : {m : ℕ} → zerof {sucn m} ≢ sucf (zerof {m})
prfn ()

noComp : {m n : ℕ} → m ℕ< n → n ℕ≤ m → ⊥
noComp {_} {0} ()
noComp {m} {suc n} p q = noteq m (suc n)
  p (eq_comm (antisymm m (suc n) (next≤ {m} {suc n} p) q))

strongTrans : {i j k : ℕ} → i ℕ≤ j → j ℕ< k → i ℕ< k
strongTrans {i} {j} {k} p q = trans_≤ {suc i} {suc j} {k} (s≤s p) q

applyToSum : {A B C D : Set} → (f : A → B) → (g : C → D) → A ⊎ C → B ⊎ D
applyToSum f g (inj₁ x) = inj₁ (f x)
applyToSum f g (inj₂ y) = inj₂ (g y)

ncom : {A : Set} → {i j : A} → i ≢ j → j ≢ i
ncom prf = λ p → prf (eq_comm p)

----------------
-- 4. Фильтрованный список короче оригинального
----------------

lemma_raz : {m n : ℕ} → m ℕ≤ n → m ℕ≤ suc n
lemma_raz z≤n = z≤n
lemma_raz (s≤s p) = s≤s (lemma_raz p)

lemma_dva : {m n : ℕ}  → m ℕ≤ n → suc m ℕ≤ suc n
lemma_dva z≤n = s≤s z≤n
lemma_dva (s≤s p) = s≤s (lemma_dva p)

sublistSmaller : {A : Set} → {ls : List A} → {l : List A} →
  ls ⊆ l → length ls ℕ≤ length l
sublistSmaller stop = z≤n
sublistSmaller (drop {x} {ls} {l} p) = lemma_raz
  {length ls}
  {length l}
  (sublistSmaller p)
sublistSmaller (keep {x} {ls} {l} p) = lemma_dva
  {length ls}
  {length l}
  (sublistSmaller p)

filterSmaller : {n : ℕ} → (i j : Fin n) → (l : List (BorderedNlist n)) →
  length (cmpFilter i j l) ℕ≤ length l
filterSmaller i j l = sublistSmaller (filterIn i j l)

----------------
-- 5. Глубина сыновей алгоритма невелика
----------------

leftSon : {n : ℕ} → {l : List (BorderedNlist n)} → {i j : Fin n} → {p : i ≢ j} →
  (a1 : Alg (cmpFilter i j l)) → (a2 : Alg (cmpFilter j i l)) →
  suc (depth a1) ℕ≤ depth {n} {l} (node i j p a1 a2)

leftSon {n} {l} {i} {j} {p} a1 a2 = trans_≤_eq
  {suc (depth {n} {cmpFilter i j l} a1)}
  {suc ((depth {n} {cmpFilter i j l} a1) ⊔⊔ (depth {n} {cmpFilter j i l} a2))}
  {depth {n} {l} (node i j p a1 a2)}
  (s≤s (m≤m⊔n (depth a1) (depth a2)))
  refl

--

rightSon : {n : ℕ} → {l : List (BorderedNlist n)} → {i j : Fin n} → {p : i ≢ j} →
  (a1 : Alg (cmpFilter i j l)) → (a2 : Alg (cmpFilter j i l)) →
  suc (depth a2) ℕ≤ depth {n} {l} (node i j p a1 a2)

rightSon {n} {l} {i} {j} {p} a1 a2 = trans_≤_eq
  {suc (depth {n} {cmpFilter j i l} a2)}
  {suc ((depth {n} {cmpFilter i j l} a1) ⊔⊔ (depth {n} {cmpFilter j i l} a2))}
  {depth {n} {l} (node i j p a1 a2)}
  (s≤s (n≤m⊔n (depth a1) (depth a2)))
  refl

----------------
-- 6. Бредим, если сортируем 1 элемент
----------------

netreb : (i j : Fin 1) → (i ≢ j) →
  (noexist (cmpFilter i j (zero — «» ∷ [])) 1 ⊎ noexist (cmpFilter j i (zero — «» ∷ [])) 1)
netreb zerof zerof p = ⊥-elim (p refl)
netreb (sucf p) _ _ = ⊥-elim (nolify p)
netreb _ (sucf q) _ = ⊥-elim (nolify q)

strange : noexist ((zerof  — «») ∷ []) 2
strange = pereh (zero — «» ∷ []) 1 netreb

----------------
-- 7. Не сортируется — длины хотя бы 2
----------------

noexistBigLength : {n : ℕ} → {l : List (BorderedNlist n)} → {dep : ℕ} →
  (2 ℕ≤ n) → (noexist l dep) → 1 ℕ< length l

noexistBigLength geq (basa l d prf) = strongTrans
  {1} {2 ^ d} {length l}
  (1≤deg d) prf

noexistBigLength {0} {l} {d} p _ = ⊥-elim (noComp (s≤s z≤n) p)
noexistBigLength {1} {l} {d} p _ = ⊥-elim (noComp (s≤s (s≤s z≤n)) p)

noexistBigLength {suc (suc n)} {l} {suc dep} geq (pereh .l .dep f)
  with (f zerof (sucf zerof) prfn)
--
... | inj₁ NOEX = trans_≤
  {2} {length (cmpFilter zero (suc zero) l)} {length l}
  (noexistBigLength geq NOEX) (filterSmaller zero (suc zero) l)
--
... | inj₂ NOEXREV = trans_≤
  {2} {length (cmpFilter (suc zero) zero l)} {length l}
  (noexistBigLength geq NOEXREV) (filterSmaller (suc zero) zero l)

----------------
-- 8. Понижение невозможной глубины
----------------

decreaseDepth : {n : ℕ} → {l : List (BorderedNlist n)} → {dep : ℕ} →
  (n ≥ 2) → noexist l (suc dep) → noexist l dep

decreaseDepth {n} {l} {d} neq (basa .l .(suc d) p) = basa l d (trans_≤
  {suc (2 ^ d)} {suc (2 ^ suc d)} {length l}
  (s≤s (degs_ineq {d} {suc d} (stepup d))) p)
decreaseDepth {n} {l} {zero} neq (pereh .l .zero F) = basa l zero
  (noexistBigLength neq (pereh l zero F))
decreaseDepth {n} {l} {sucn m} neq (pereh .l .(sucn m) F) = pereh l m
  (λ i j p → applyToSum (decreaseDepth neq) (decreaseDepth neq) (F i j p))

----------------
-- 9. Отсутствие алгоритма из-за noexist
----------------

noexistNoAlg : {n : ℕ} → {l : List (BorderedNlist n)} → {dep : ℕ} →
  (2 ℕ≤ n) → Unicalized l → noexist l dep →
  (a : Alg l) → (depth a ℕ≤ dep) → ⊥

noexistNoAlg neq u (basa l d p) a q = noComp
  {2 ^ d} {length l}
  p (trans_≤ (len2depth a u) (degs_ineq q))

noexistNoAlg {n} {l} {suc d} neq u (pereh .l .d f) (node i j prf a1 a2) q with (f i j prf)
--
... | inj₁ NOEX = noexistNoAlg
    neq
    (filterUnic i j l u) NOEX a1
    (decrease≤ {depth a1} {d} (trans_≤ (leftSon {n} {l} {i} {j} {prf} a1 a2) q))
--
... | inj₂ NOEXREV = noexistNoAlg
    neq
    (filterUnic j i l u) NOEXREV a2
    (decrease≤ {depth a2} {d} (trans_≤ (rightSon {n} {l} {i} {j} {prf} a1 a2) q))

noexistNoAlg neq u (pereh (.b ∷ []) d f) (leaf b) q = noteq
  1 (length (b ∷ []))
  (noexistBigLength neq (pereh (b ∷ []) d f)) refl
