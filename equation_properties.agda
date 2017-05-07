----------------
-- Необходимые свойства
-- равенства и неравенств
----------------

module equation_properties where

open import Agda.Primitive
open import Data.Bool
open import IO.Primitive using (IO; putStrLn)
open import Foreign.Haskell using (Unit)

open import Data.Nat using (ℕ; _∸_; suc; pred; zero)
open import Data.Nat.Base using (_*_; _<_; _≰_) 
open import Data.Nat.Base renaming (_≤_ to _ℕ≤_; _+_ to _+n_)
open import Data.Nat.Base public using (z≤n; s≤s)
open import Data.Nat.Properties using (m≢1+m+n; m≤m+n; _+-mono_)

open import Data.Fin
open import Data.Fin renaming (zero to zerof; suc to sucf; inject₁ to inj)
open import Data.Fin renaming (_<_ to _lessThan_; _≤_ to _lessEq_)

open import Data.List using (List; []; _++_)
open import Data.List.Base using (_∷_; filter)
open import Relation.Binary.Core public using (_≡_; refl; _≢_)
open import Relation.Nullary.Negation
open import Data.Empty

----------------
-- Арифметические операции
----------------

_⊔⊔_ = Data.Nat._⊔_

_^_ : ℕ → ℕ → ℕ
n ^ 0 = 1
n ^ (suc m) = (n ^ m) * n

----------------
-- Свойства равенства
----------------

eq_comm : ∀ {P : Set} {m n : P} → (m ≡ n) → (n ≡ m)
eq_comm refl = refl

eq_trans : ∀ {A : Set} {a b c : A} → a ≡ b → b ≡ c → a ≡ c
eq_trans refl refl = refl

eq_cong : ∀ {P Q : Set} {m n : P} → (f : P → Q) → m ≡ n → (f m ≡ f n)
eq_cong f refl = refl

preserv-+ : ∀ {m n x y : ℕ} → (m ≡ n) → (x ≡ y) → (m Data.Nat.+ x ≡ n Data.Nat.+ y)
preserv-+ refl refl = refl

----------------
-- Рефлексивность, антисимметричность,
-- транзитивность неравенства
----------------

≤-refl : {a : ℕ} → a ℕ≤ a
≤-refl {0} = z≤n
≤-refl {suc m} = s≤s (≤-refl {m})

antisymm : (m n : ℕ) → m Data.Nat.≤ n → n Data.Nat.≤ m → n ≡ m
antisymm 0 0 p q = refl
antisymm (suc x) 0 ()
antisymm 0 (suc x) p ()
antisymm (suc x) (suc y) (s≤s p) (s≤s q) = eq_cong (suc) (antisymm x y p q)

trans_≤ : ∀ {a b c : ℕ} → (a ℕ≤ b) → (b ℕ≤ c) → (a ℕ≤ c)
trans_≤ z≤n _ = z≤n
trans_≤ (s≤s a) (s≤s b) = s≤s (trans_≤ a b)

----------------
-- Навёрнутые транзитивности
----------------

trans_≤_eq : ∀ {a b c : ℕ} → (a ℕ≤ b) → (b ≡ c) → (a ℕ≤ c)
trans_≤_eq p refl = p

trans_difficult : {a b c d : ℕ} → (a ≡ b) → (b ℕ≤ c) → (c ≡ d) → (a ℕ≤ d)
trans_difficult refl q refl = q

----------------
-- Операции, сохраняющие неравенство
----------------

preserv : ∀ {m n x y : ℕ} → (m ℕ≤ n) → (x ℕ≤ y) → (m +n x ℕ≤ n +n y)
preserv  P Q = P +-mono Q

n≤m⊔n : ∀ m n → n ℕ≤ m ⊔⊔ n
n≤m⊔n n zero       = z≤n
n≤m⊔n zero (suc m)    = ≤-refl
n≤m⊔n (suc x) (suc y) = s≤s (n≤m⊔n x y)

----------------
-- О противоречивых утверждениях
----------------

nolify : Fin 0 → ⊥
nolify ()

noteq : (m n : ℕ) → m Data.Nat.< n → m ≡ n → ⊥
noteq 0 0 ()
noteq (suc x) 0 ()
noteq 0 (suc x) p ()
noteq (suc x) (suc y) (s≤s p) q = noteq x y p (eq_cong (Data.Nat.pred) q)
