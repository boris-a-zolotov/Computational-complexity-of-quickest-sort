----------------
-- Длина фильтруемого списка
----------------

module final_length where

open import Agda.Primitive
open import Data.Bool
open import IO.Primitive using (IO; putStrLn)
open import Foreign.Haskell using (Unit)

open import Data.Nat using (ℕ; _∸_; zero)
open import Data.Nat renaming (suc to sucn; pred to predn)
open import Data.Nat renaming (_+_ to _+n_; _≤_ to _ℕ≤_ )
open import Data.Nat.Base using (_*_; _<_; _≰_) 
open import Data.Nat.Base public using (z≤n; s≤s)
open import Data.Nat.Properties using (m≢1+m+n; m≤m+n; _+-mono_)
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

open import filter_length
open import permutation_definition
open import equation_properties

----------------
-- Во всех перестановках списка
-- различны все элементы
----------------

data Unicalized : {n : ℕ} → List (BorderedNlist n) → Set where
  u-nil : {n : ℕ} → Unicalized {n} []
  _u-cons_ : {n : ℕ} → {l : List (BorderedNlist n)} →
    {x : BorderedNlist n} → ((i j : Fin n) → (i ≢ j) → nth x i ≢ nth x j) → Unicalized l →
    Unicalized (x ∷ l)

----------------
-- Если два числа доказательно сравнимы,
-- то у них правильный ордеринг
----------------

congNumCmp : {n : ℕ} → (i j : Fin n) → (b : Bool) → (numCmp i j ≡ b) → (numCmp (sucf i) (sucf j) ≡ b)
congNumCmp zerof zerof true ()
congNumCmp zerof zerof false _ = refl
congNumCmp zerof (sucf j) true p = refl
congNumCmp zerof (sucf j) false ()
congNumCmp (sucf i) zerof false p = refl
congNumCmp (sucf i) zerof true ()
congNumCmp (sucf i) (sucf j) b p with cmpFin i j
congNumCmp (sucf .(inject least)) (sucf .greatest) true p | less greatest least = refl 
congNumCmp (sucf .(inject least)) (sucf .greatest) false () | less greatest least
congNumCmp (sucf .greatest) (sucf .(inject least)) true () | greater greatest least
congNumCmp (sucf .greatest) (sucf .(inject least)) false p | greater greatest least = refl
congNumCmp (sucf .i) (sucf .i) true () | equal i
congNumCmp (sucf .i) (sucf .i) false p | equal i = refl

correctLessCmp : {n : ℕ} → (a b : Fin n) → (p : a lessThan b) → (numCmp a b ≡ true)
correctLessCmp zerof (sucf b) p = refl
correctLessCmp _ (zerof ) ()
correctLessCmp (sucf a) (sucf b) (s≤s p) = congNumCmp a b true (correctLessCmp a b p)

----------------
-- Непременно выполнено одно из двух
-- высокоуровневых неравенств
----------------

oneOfComps : {n : ℕ} → (i j : Fin n) → (i ≢ j) → (numCmp i j ≡ true) ⊎ (numCmp j i ≡ true)
oneOfComps i j prf with (oneOfInequiv i j prf)
... | inj₁ p = inj₁ (correctLessCmp i j p)
... | inj₂ q = inj₂ (correctLessCmp j i q)

oneOfListComps : {n : ℕ} → (i j : Fin n) → (l : BorderedNlist n) → (nth l i ≢ nth l j) →
  (listCmp i j l ≡ true) ⊎ (listCmp j i l ≡ true)
oneOfListComps {n} i j l p with (oneOfComps (nth l i) (nth l j) p)
... | inj₁ g = inj₁ (eq_trans {Bool} {listCmp i j l} {numCmp (nth l i) (nth l j)} {true} refl g)
... | inj₂ g = inj₂ (eq_trans {Bool} {listCmp j i l} {numCmp (nth l j) (nth l i)} {true} refl g)

----------------
-- Очевидные свойства сравнения
----------------

suc≤ : (x : ℕ) → x ℕ≤ (sucn x)
suc≤ zero = z≤n
suc≤ (sucn x) = s≤s (suc≤ x)

me≤ : (m n : ℕ) → (m ≡ n) → (m ℕ≤ n)
me≤ 0 0 p = z≤n
me≤ 0 (suc n) ()
me≤ (suc m) 0 ()
me≤ (suc m) (suc n) p = s≤s (me≤ m n (eq_cong predn p))

trans_d : {a b c d : ℕ} → (a ≡ b) → (b ℕ≤ c) → (c ℕ≤ d) → (a ℕ≤ d)
trans_d refl p q = trans_≤ p q

----------------
-- Длина фильтрованного списка
-- не уменьшается при добавлении головы
----------------

cmpTOF : ∀ {n} → ∀ i j → ∀ x → (listCmp {n} i j x ≡ true) ⊎ (listCmp i j x ≡ false)
cmpTOF i j x with listCmp i j x
... | true = inj₁ refl
... | false = inj₂ refl

anythingLength : ∀ {n} → ∀ i j → ∀ x → ∀ ls →
  length (cmpFilter {n} i j ls)  ℕ≤  length (cmpFilter {n} i j (x ∷ ls))

anythingLength {n} i j x ls with (cmpTOF i j x)
... | inj₁ prf = trans_≤_eq
  {length (cmpFilter {n} i j ls)}
  {suc (length (cmpFilter {n} i j ls))}
  {length (cmpFilter {n} i j (x ∷ ls))}
  (suc≤ (length (cmpFilter {n} i j ls)))
  (eq_comm (addLength {n} i j x ls prf))
... | inj₂ prf = me≤
  (length (cmpFilter {n} i j ls))
  (length (cmpFilter {n} i j (x ∷ ls)))
  (eq_comm (dropLength {n} i j x ls prf))

----------------
-- Длина списка не превосходит
-- суммы длин фильтрованных
----------------

FILTERLENGTH : {n : ℕ} → ∀ i j → (i ≢ j) → ∀ lis → Unicalized lis →
  length lis ℕ≤ length (cmpFilter {n} i j lis) +n length (cmpFilter {n} j i lis)

FILTERLENGTH {n} i j pn [] u-nil = me≤
  (length {_} {BorderedNlist n} [])
  (length (cmpFilter i j []) +n length (cmpFilter j i []))
  refl

FILTERLENGTH {n} i j pn (x ∷ ls) (f u-cons u) with (oneOfListComps i j x (f i j pn))
... | inj₁ prftrue = trans_d

  {length (x ∷ ls)}
  {suc (length ls)}
  {suc (length (cmpFilter {n} i j ls)) +n length (cmpFilter {n} j i ls)}
  {length (cmpFilter {n} i j (x ∷ ls)) +n length (cmpFilter {n} j i (x ∷ ls))}

  refl
  (trans_≤_eq
    (s≤s (FILTERLENGTH i j pn ls u))
    (suc+x (length (cmpFilter {n} i j ls)) (length (cmpFilter {n} j i ls))))
  (preserv
    {suc (length (cmpFilter {n} i j ls))}
    {length (cmpFilter {n} i j (x ∷ ls))}
    {length (cmpFilter {n} j i ls)}
    {length (cmpFilter {n} j i (x ∷ ls))}

    (me≤ (suc (length (cmpFilter {n} i j ls))) (length (cmpFilter {n} i j (x ∷ ls)))
      (eq_comm (addLength {n} i j x ls prftrue)))
    (anythingLength {n} j i x ls))

... | inj₂ prfoppos = trans_d

  {length (x ∷ ls)}
  {suc (length ls)}
  {length (cmpFilter {n} i j ls) +n suc (length (cmpFilter {n} j i ls))}
  {length (cmpFilter {n} i j (x ∷ ls)) +n length (cmpFilter {n} j i (x ∷ ls))}

  refl
  (trans_≤_eq
    (s≤s (FILTERLENGTH i j pn ls u))
    (x+suc (length (cmpFilter {n} i j ls)) (length (cmpFilter {n} j i ls))))
  (preserv
    {length (cmpFilter {n} i j ls)}
    {length (cmpFilter {n} i j (x ∷ ls))}
    {suc (length (cmpFilter {n} j i ls))}
    {length (cmpFilter {n} j i (x ∷ ls))}

    (anythingLength {n} i j x ls)
    (me≤ (suc (length (cmpFilter {n} j i ls))) (length (cmpFilter {n} j i (x ∷ ls)))
      (eq_comm (addLength {n} j i x ls prfoppos))))
