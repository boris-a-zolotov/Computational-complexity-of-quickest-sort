----------------
-- Алгоритм
----------------

module algorithm where

open import Agda.Primitive
open import Data.Bool
open import IO.Primitive using (IO; putStrLn)
open import Foreign.Haskell using (Unit)

open import Data.Nat using (ℕ; _+_; _∸_; suc; pred; zero)
open import Data.Nat.Base using (_*_; _<_; _≤_; _≰_) 
open import Data.Nat.Base public using (z≤n; s≤s)
open import Data.Nat.Properties using (m≢1+m+n; m≤m+n)

open import Data.Fin
open import Data.Fin renaming (zero to zerof; suc to sucf; pred to predf; inject₁ to inj)
open import Data.Fin renaming (_<_ to _lessThan_; _≤_ to _lessEq_)

open import Data.List using (List; []; _++_)
open import Data.List.Base using (_∷_; filter)
open import Relation.Binary.Core public using (_≡_; refl; _≢_)
open import Relation.Nullary.Negation
open import Data.Empty

open import permutation_definition
open import equation_properties

----------------
-- Определение алгоритма
----------------

data Alg : {n : ℕ} → List (BorderedNlist n) → Set where
  leaf : {n : ℕ} → (b : BorderedNlist n) → Alg (b ∷ [])
  node : {n : ℕ} → {l : List (BorderedNlist n)} → (i j : Fin n) → (i ≢ j) → Alg (cmpFilter i j l) → Alg (cmpFilter j i l) → Alg l

----------------
-- Конкретный пример: перестановки 5
----------------

testp30142 : BorderedNlist 5
testp30142 = (sucf (sucf (sucf zerof))) — (zerof — (sucf zerof — (sucf (sucf (sucf (sucf zerof))) — (sucf (sucf zerof) — «»))))

testp43021 : BorderedNlist 5
testp43021 = (sucf (sucf (sucf (sucf zerof)))) — ((sucf (sucf (sucf zerof))) — (zerof — ((sucf (sucf zerof)) — ((sucf zerof) — «»))))

prf12 : sucf (zerof {3}) ≢ sucf (sucf (zerof {2}))
prf12 = λ P → noteq (toℕ (sucf (zerof {4}))) (toℕ (sucf (sucf (zerof {3})))) (s≤s (s≤s z≤n)) (eq_cong toℕ P)

testalg5 : Alg (testp30142 ∷ testp43021 ∷ [])
testalg5 = node (suc zero) (suc (suc zero)) prf12 (leaf testp30142) (leaf testp43021)

----------------
-- Конкретный пример: перестановки 3
----------------

nul : Fin 3
nul = zerof

raz : Fin 3
raz = sucf zerof

dva : Fin 3
dva = sucf (sucf zerof)

--

p012 : BorderedNlist 3
p012 = nul — (raz — (dva — «»))

p021 : BorderedNlist 3
p021 = nul — (dva — (raz — «»))

p102 : BorderedNlist 3
p102 = raz — (nul — (dva — «»))

p120 : BorderedNlist 3
p120 = raz — (dva — (nul — «»))

p201 : BorderedNlist 3
p201 = dva — (nul — (raz — «»))

--

prf3-01 : zerof {2} ≢ sucf (zerof {1})
prf3-01 = λ P → noteq
  (toℕ (zero {2}))
  (toℕ (suc (zero {1})))
  (s≤s z≤n)
  (eq toℕ cong P)

prf3-02 : zerof {2} ≢ sucf (sucf (zerof {0}))
prf3-02 = λ P → noteq
  (toℕ (zero {2}))
  (toℕ (suc (suc (zero {0}))))
  (s≤s z≤n)
  (eq toℕ cong P)

prf3-12 : sucf (zerof {1}) ≢ sucf (sucf (zero {0}))
prf3-12 = λ P → noteq
  (toℕ (sucf (zero {1})))
  (toℕ (suc (suc (zero {0}))))
  (s≤s (s≤s z≤n))
  (eq toℕ cong P)

--

testalg3 : Alg (p012 ∷ p021 ∷ p120 ∷ p201 ∷ p102 ∷ [])
testalg3 = node zero (suc zero) prf3-01
  (node (suc zero) (suc (suc zero)) prf3-12
    (leaf p012)
    (node zero (suc (suc zero)) prf3-02
      (leaf p021)
      (leaf p120)))
  (node zero (suc (suc zero)) prf3-02
    (leaf p102)
    (leaf p201))
