----------------
-- Сортировка всех перестановок длины 5
----------------

module allperms_sorted where

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
-- Элементы типа Fin 5 попарно различны
----------------

prfNoteq5--0,1 : zerof {4} ≢ sucf (zerof {3})
prfNoteq5--0,1 = λ P → noteq
  (toℕ (zerof {4}))
  (toℕ (sucf (zerof {3})))
  (s≤s z≤n)
  (eq_cong toℕ P)

prfNoteq5--0,2 : zerof {4} ≢ sucf (sucf (zerof {2}))
prfNoteq5--0,2 = λ P → noteq
  (toℕ (zerof {4}))
  (toℕ (sucf (sucf (zerof {2}))))
  (s≤s z≤n)
  (eq_cong toℕ P)

prfNoteq5--0,3 : zerof {4} ≢ sucf (sucf (sucf (zerof {1})))
prfNoteq5--0,3 = λ P → noteq
  (toℕ (zerof {4}))
  (toℕ (sucf (sucf (sucf (zerof {1})))))
  (s≤s z≤n)
  (eq_cong toℕ P)

prfNoteq5--0,4 : zerof {4} ≢ sucf (sucf (sucf (sucf (zerof {0}))))
prfNoteq5--0,4 = λ P → noteq
  (toℕ (zerof {4}))
  (toℕ (sucf (sucf (sucf (sucf (zerof {0}))))))
  (s≤s z≤n)
  (eq_cong toℕ P)

prfNoteq5--1,2 : sucf (zerof {3}) ≢ sucf (sucf (zerof {2}))
prfNoteq5--1,2 = λ P → noteq
  (toℕ (sucf (zerof {3})))
  (toℕ (sucf (sucf (zerof {2}))))
  (s≤s (s≤s z≤n))
  (eq_cong toℕ P)

prfNoteq5--1,3 : sucf (zerof {3}) ≢ sucf (sucf (sucf (zerof {1})))
prfNoteq5--1,3 = λ P → noteq
  (toℕ (sucf (zerof {3})))
  (toℕ (sucf (sucf (sucf (zerof {1})))))
  (s≤s (s≤s z≤n))
  (eq_cong toℕ P)

prfNoteq5--1,4 : sucf (zerof {3}) ≢ sucf (sucf (sucf (sucf (zerof {0}))))
prfNoteq5--1,4 = λ P → noteq
  (toℕ (sucf (zerof {3})))
  (toℕ (sucf (sucf (sucf (sucf (zerof {0}))))))
  (s≤s (s≤s z≤n))
  (eq_cong toℕ P)

prfNoteq5--2,3 : sucf (sucf (zerof {2})) ≢ sucf (sucf (sucf (zerof {1})))
prfNoteq5--2,3 = λ P → noteq
  (toℕ (sucf (sucf (zerof {2}))))
  (toℕ (sucf (sucf (sucf (zerof {1})))))
  (s≤s (s≤s (s≤s z≤n)))
  (eq_cong toℕ P)

prfNoteq5--2,4 : sucf (sucf (zerof {2})) ≢ sucf (sucf (sucf (sucf (zerof {0}))))
prfNoteq5--2,4 = λ P → noteq
  (toℕ (sucf (sucf (zerof {2}))))
  (toℕ (sucf (sucf (sucf (sucf (zerof {0}))))))
  (s≤s (s≤s (s≤s z≤n)))
  (eq_cong toℕ P)

prfNoteq5--3,4 : sucf (sucf (sucf (zerof {1}))) ≢ sucf (sucf (sucf (sucf (zerof {0}))))
prfNoteq5--3,4 = λ P → noteq
  (toℕ (sucf (sucf (sucf (zerof {1})))))
  (toℕ (sucf (sucf (sucf (sucf (zerof {0}))))))
  (s≤s (s≤s (s≤s (s≤s z≤n))))
  (eq_cong toℕ P)

----------------
-- Представление элементов списка и его самого
----------------

p_0,1,2,3,4 = zerof {4} — ((sucf (zerof {3})) — ((sucf (sucf (zerof {2}))) — ((sucf (sucf (sucf (zerof {1})))) — ((sucf (sucf (sucf (sucf (zerof {0}))))) — «»))))

p_0,1,2,4,3 = zerof {4} — ((sucf (zerof {3})) — ((sucf (sucf (zerof {2}))) — ((sucf (sucf (sucf (sucf (zerof {0}))))) — ((sucf (sucf (sucf (zerof {1})))) — «»))))

p_0,1,3,2,4 = zerof {4} — ((sucf (zerof {3})) — ((sucf (sucf (sucf (zerof {1})))) — ((sucf (sucf (zerof {2}))) — ((sucf (sucf (sucf (sucf (zerof {0}))))) — «»))))

p_0,1,3,4,2 = zerof {4} — ((sucf (zerof {3})) — ((sucf (sucf (sucf (zerof {1})))) — ((sucf (sucf (sucf (sucf (zerof {0}))))) — ((sucf (sucf (zerof {2}))) — «»))))

p_0,1,4,2,3 = zerof {4} — ((sucf (zerof {3})) — ((sucf (sucf (sucf (sucf (zerof {0}))))) — ((sucf (sucf (zerof {2}))) — ((sucf (sucf (sucf (zerof {1})))) — «»))))

p_0,1,4,3,2 = zerof {4} — ((sucf (zerof {3})) — ((sucf (sucf (sucf (sucf (zerof {0}))))) — ((sucf (sucf (sucf (zerof {1})))) — ((sucf (sucf (zerof {2}))) — «»))))

p_0,2,1,3,4 = zerof {4} — ((sucf (sucf (zerof {2}))) — ((sucf (zerof {3})) — ((sucf (sucf (sucf (zerof {1})))) — ((sucf (sucf (sucf (sucf (zerof {0}))))) — «»))))

p_0,2,1,4,3 = zerof {4} — ((sucf (sucf (zerof {2}))) — ((sucf (zerof {3})) — ((sucf (sucf (sucf (sucf (zerof {0}))))) — ((sucf (sucf (sucf (zerof {1})))) — «»))))

p_0,2,3,1,4 = zerof {4} — ((sucf (sucf (zerof {2}))) — ((sucf (sucf (sucf (zerof {1})))) — ((sucf (zerof {3})) — ((sucf (sucf (sucf (sucf (zerof {0}))))) — «»))))

p_0,2,3,4,1 = zerof {4} — ((sucf (sucf (zerof {2}))) — ((sucf (sucf (sucf (zerof {1})))) — ((sucf (sucf (sucf (sucf (zerof {0}))))) — ((sucf (zerof {3})) — «»))))

p_0,2,4,1,3 = zerof {4} — ((sucf (sucf (zerof {2}))) — ((sucf (sucf (sucf (sucf (zerof {0}))))) — ((sucf (zerof {3})) — ((sucf (sucf (sucf (zerof {1})))) — «»))))

p_0,2,4,3,1 = zerof {4} — ((sucf (sucf (zerof {2}))) — ((sucf (sucf (sucf (sucf (zerof {0}))))) — ((sucf (sucf (sucf (zerof {1})))) — ((sucf (zerof {3})) — «»))))

p_0,3,1,2,4 = zerof {4} — ((sucf (sucf (sucf (zerof {1})))) — ((sucf (zerof {3})) — ((sucf (sucf (zerof {2}))) — ((sucf (sucf (sucf (sucf (zerof {0}))))) — «»))))

p_0,3,1,4,2 = zerof {4} — ((sucf (sucf (sucf (zerof {1})))) — ((sucf (zerof {3})) — ((sucf (sucf (sucf (sucf (zerof {0}))))) — ((sucf (sucf (zerof {2}))) — «»))))

p_0,3,2,1,4 = zerof {4} — ((sucf (sucf (sucf (zerof {1})))) — ((sucf (sucf (zerof {2}))) — ((sucf (zerof {3})) — ((sucf (sucf (sucf (sucf (zerof {0}))))) — «»))))

p_0,3,2,4,1 = zerof {4} — ((sucf (sucf (sucf (zerof {1})))) — ((sucf (sucf (zerof {2}))) — ((sucf (sucf (sucf (sucf (zerof {0}))))) — ((sucf (zerof {3})) — «»))))

p_0,3,4,1,2 = zerof {4} — ((sucf (sucf (sucf (zerof {1})))) — ((sucf (sucf (sucf (sucf (zerof {0}))))) — ((sucf (zerof {3})) — ((sucf (sucf (zerof {2}))) — «»))))

p_0,3,4,2,1 = zerof {4} — ((sucf (sucf (sucf (zerof {1})))) — ((sucf (sucf (sucf (sucf (zerof {0}))))) — ((sucf (sucf (zerof {2}))) — ((sucf (zerof {3})) — «»))))

p_0,4,1,2,3 = zerof {4} — ((sucf (sucf (sucf (sucf (zerof {0}))))) — ((sucf (zerof {3})) — ((sucf (sucf (zerof {2}))) — ((sucf (sucf (sucf (zerof {1})))) — «»))))

p_0,4,1,3,2 = zerof {4} — ((sucf (sucf (sucf (sucf (zerof {0}))))) — ((sucf (zerof {3})) — ((sucf (sucf (sucf (zerof {1})))) — ((sucf (sucf (zerof {2}))) — «»))))

p_0,4,2,1,3 = zerof {4} — ((sucf (sucf (sucf (sucf (zerof {0}))))) — ((sucf (sucf (zerof {2}))) — ((sucf (zerof {3})) — ((sucf (sucf (sucf (zerof {1})))) — «»))))

p_0,4,2,3,1 = zerof {4} — ((sucf (sucf (sucf (sucf (zerof {0}))))) — ((sucf (sucf (zerof {2}))) — ((sucf (sucf (sucf (zerof {1})))) — ((sucf (zerof {3})) — «»))))

p_0,4,3,1,2 = zerof {4} — ((sucf (sucf (sucf (sucf (zerof {0}))))) — ((sucf (sucf (sucf (zerof {1})))) — ((sucf (zerof {3})) — ((sucf (sucf (zerof {2}))) — «»))))

p_0,4,3,2,1 = zerof {4} — ((sucf (sucf (sucf (sucf (zerof {0}))))) — ((sucf (sucf (sucf (zerof {1})))) — ((sucf (sucf (zerof {2}))) — ((sucf (zerof {3})) — «»))))

p_1,0,2,3,4 = (sucf (zerof {3})) — (zerof {4} — ((sucf (sucf (zerof {2}))) — ((sucf (sucf (sucf (zerof {1})))) — ((sucf (sucf (sucf (sucf (zerof {0}))))) — «»))))

p_1,0,2,4,3 = (sucf (zerof {3})) — (zerof {4} — ((sucf (sucf (zerof {2}))) — ((sucf (sucf (sucf (sucf (zerof {0}))))) — ((sucf (sucf (sucf (zerof {1})))) — «»))))

p_1,0,3,2,4 = (sucf (zerof {3})) — (zerof {4} — ((sucf (sucf (sucf (zerof {1})))) — ((sucf (sucf (zerof {2}))) — ((sucf (sucf (sucf (sucf (zerof {0}))))) — «»))))

p_1,0,3,4,2 = (sucf (zerof {3})) — (zerof {4} — ((sucf (sucf (sucf (zerof {1})))) — ((sucf (sucf (sucf (sucf (zerof {0}))))) — ((sucf (sucf (zerof {2}))) — «»))))

p_1,0,4,2,3 = (sucf (zerof {3})) — (zerof {4} — ((sucf (sucf (sucf (sucf (zerof {0}))))) — ((sucf (sucf (zerof {2}))) — ((sucf (sucf (sucf (zerof {1})))) — «»))))

p_1,0,4,3,2 = (sucf (zerof {3})) — (zerof {4} — ((sucf (sucf (sucf (sucf (zerof {0}))))) — ((sucf (sucf (sucf (zerof {1})))) — ((sucf (sucf (zerof {2}))) — «»))))

p_1,2,0,3,4 = (sucf (zerof {3})) — ((sucf (sucf (zerof {2}))) — (zerof {4} — ((sucf (sucf (sucf (zerof {1})))) — ((sucf (sucf (sucf (sucf (zerof {0}))))) — «»))))

p_1,2,0,4,3 = (sucf (zerof {3})) — ((sucf (sucf (zerof {2}))) — (zerof {4} — ((sucf (sucf (sucf (sucf (zerof {0}))))) — ((sucf (sucf (sucf (zerof {1})))) — «»))))

p_1,2,3,0,4 = (sucf (zerof {3})) — ((sucf (sucf (zerof {2}))) — ((sucf (sucf (sucf (zerof {1})))) — (zerof {4} — ((sucf (sucf (sucf (sucf (zerof {0}))))) — «»))))

p_1,2,3,4,0 = (sucf (zerof {3})) — ((sucf (sucf (zerof {2}))) — ((sucf (sucf (sucf (zerof {1})))) — ((sucf (sucf (sucf (sucf (zerof {0}))))) — (zerof {4} — «»))))

p_1,2,4,0,3 = (sucf (zerof {3})) — ((sucf (sucf (zerof {2}))) — ((sucf (sucf (sucf (sucf (zerof {0}))))) — (zerof {4} — ((sucf (sucf (sucf (zerof {1})))) — «»))))

p_1,2,4,3,0 = (sucf (zerof {3})) — ((sucf (sucf (zerof {2}))) — ((sucf (sucf (sucf (sucf (zerof {0}))))) — ((sucf (sucf (sucf (zerof {1})))) — (zerof {4} — «»))))

p_1,3,0,2,4 = (sucf (zerof {3})) — ((sucf (sucf (sucf (zerof {1})))) — (zerof {4} — ((sucf (sucf (zerof {2}))) — ((sucf (sucf (sucf (sucf (zerof {0}))))) — «»))))

p_1,3,0,4,2 = (sucf (zerof {3})) — ((sucf (sucf (sucf (zerof {1})))) — (zerof {4} — ((sucf (sucf (sucf (sucf (zerof {0}))))) — ((sucf (sucf (zerof {2}))) — «»))))

p_1,3,2,0,4 = (sucf (zerof {3})) — ((sucf (sucf (sucf (zerof {1})))) — ((sucf (sucf (zerof {2}))) — (zerof {4} — ((sucf (sucf (sucf (sucf (zerof {0}))))) — «»))))

p_1,3,2,4,0 = (sucf (zerof {3})) — ((sucf (sucf (sucf (zerof {1})))) — ((sucf (sucf (zerof {2}))) — ((sucf (sucf (sucf (sucf (zerof {0}))))) — (zerof {4} — «»))))

p_1,3,4,0,2 = (sucf (zerof {3})) — ((sucf (sucf (sucf (zerof {1})))) — ((sucf (sucf (sucf (sucf (zerof {0}))))) — (zerof {4} — ((sucf (sucf (zerof {2}))) — «»))))

p_1,3,4,2,0 = (sucf (zerof {3})) — ((sucf (sucf (sucf (zerof {1})))) — ((sucf (sucf (sucf (sucf (zerof {0}))))) — ((sucf (sucf (zerof {2}))) — (zerof {4} — «»))))

p_1,4,0,2,3 = (sucf (zerof {3})) — ((sucf (sucf (sucf (sucf (zerof {0}))))) — (zerof {4} — ((sucf (sucf (zerof {2}))) — ((sucf (sucf (sucf (zerof {1})))) — «»))))

p_1,4,0,3,2 = (sucf (zerof {3})) — ((sucf (sucf (sucf (sucf (zerof {0}))))) — (zerof {4} — ((sucf (sucf (sucf (zerof {1})))) — ((sucf (sucf (zerof {2}))) — «»))))

p_1,4,2,0,3 = (sucf (zerof {3})) — ((sucf (sucf (sucf (sucf (zerof {0}))))) — ((sucf (sucf (zerof {2}))) — (zerof {4} — ((sucf (sucf (sucf (zerof {1})))) — «»))))

p_1,4,2,3,0 = (sucf (zerof {3})) — ((sucf (sucf (sucf (sucf (zerof {0}))))) — ((sucf (sucf (zerof {2}))) — ((sucf (sucf (sucf (zerof {1})))) — (zerof {4} — «»))))

p_1,4,3,0,2 = (sucf (zerof {3})) — ((sucf (sucf (sucf (sucf (zerof {0}))))) — ((sucf (sucf (sucf (zerof {1})))) — (zerof {4} — ((sucf (sucf (zerof {2}))) — «»))))

p_1,4,3,2,0 = (sucf (zerof {3})) — ((sucf (sucf (sucf (sucf (zerof {0}))))) — ((sucf (sucf (sucf (zerof {1})))) — ((sucf (sucf (zerof {2}))) — (zerof {4} — «»))))

p_2,0,1,3,4 = (sucf (sucf (zerof {2}))) — (zerof {4} — ((sucf (zerof {3})) — ((sucf (sucf (sucf (zerof {1})))) — ((sucf (sucf (sucf (sucf (zerof {0}))))) — «»))))

p_2,0,1,4,3 = (sucf (sucf (zerof {2}))) — (zerof {4} — ((sucf (zerof {3})) — ((sucf (sucf (sucf (sucf (zerof {0}))))) — ((sucf (sucf (sucf (zerof {1})))) — «»))))

p_2,0,3,1,4 = (sucf (sucf (zerof {2}))) — (zerof {4} — ((sucf (sucf (sucf (zerof {1})))) — ((sucf (zerof {3})) — ((sucf (sucf (sucf (sucf (zerof {0}))))) — «»))))

p_2,0,3,4,1 = (sucf (sucf (zerof {2}))) — (zerof {4} — ((sucf (sucf (sucf (zerof {1})))) — ((sucf (sucf (sucf (sucf (zerof {0}))))) — ((sucf (zerof {3})) — «»))))

p_2,0,4,1,3 = (sucf (sucf (zerof {2}))) — (zerof {4} — ((sucf (sucf (sucf (sucf (zerof {0}))))) — ((sucf (zerof {3})) — ((sucf (sucf (sucf (zerof {1})))) — «»))))

p_2,0,4,3,1 = (sucf (sucf (zerof {2}))) — (zerof {4} — ((sucf (sucf (sucf (sucf (zerof {0}))))) — ((sucf (sucf (sucf (zerof {1})))) — ((sucf (zerof {3})) — «»))))

p_2,1,0,3,4 = (sucf (sucf (zerof {2}))) — ((sucf (zerof {3})) — (zerof {4} — ((sucf (sucf (sucf (zerof {1})))) — ((sucf (sucf (sucf (sucf (zerof {0}))))) — «»))))

p_2,1,0,4,3 = (sucf (sucf (zerof {2}))) — ((sucf (zerof {3})) — (zerof {4} — ((sucf (sucf (sucf (sucf (zerof {0}))))) — ((sucf (sucf (sucf (zerof {1})))) — «»))))

p_2,1,3,0,4 = (sucf (sucf (zerof {2}))) — ((sucf (zerof {3})) — ((sucf (sucf (sucf (zerof {1})))) — (zerof {4} — ((sucf (sucf (sucf (sucf (zerof {0}))))) — «»))))

p_2,1,3,4,0 = (sucf (sucf (zerof {2}))) — ((sucf (zerof {3})) — ((sucf (sucf (sucf (zerof {1})))) — ((sucf (sucf (sucf (sucf (zerof {0}))))) — (zerof {4} — «»))))

p_2,1,4,0,3 = (sucf (sucf (zerof {2}))) — ((sucf (zerof {3})) — ((sucf (sucf (sucf (sucf (zerof {0}))))) — (zerof {4} — ((sucf (sucf (sucf (zerof {1})))) — «»))))

p_2,1,4,3,0 = (sucf (sucf (zerof {2}))) — ((sucf (zerof {3})) — ((sucf (sucf (sucf (sucf (zerof {0}))))) — ((sucf (sucf (sucf (zerof {1})))) — (zerof {4} — «»))))

p_2,3,0,1,4 = (sucf (sucf (zerof {2}))) — ((sucf (sucf (sucf (zerof {1})))) — (zerof {4} — ((sucf (zerof {3})) — ((sucf (sucf (sucf (sucf (zerof {0}))))) — «»))))

p_2,3,0,4,1 = (sucf (sucf (zerof {2}))) — ((sucf (sucf (sucf (zerof {1})))) — (zerof {4} — ((sucf (sucf (sucf (sucf (zerof {0}))))) — ((sucf (zerof {3})) — «»))))

p_2,3,1,0,4 = (sucf (sucf (zerof {2}))) — ((sucf (sucf (sucf (zerof {1})))) — ((sucf (zerof {3})) — (zerof {4} — ((sucf (sucf (sucf (sucf (zerof {0}))))) — «»))))

p_2,3,1,4,0 = (sucf (sucf (zerof {2}))) — ((sucf (sucf (sucf (zerof {1})))) — ((sucf (zerof {3})) — ((sucf (sucf (sucf (sucf (zerof {0}))))) — (zerof {4} — «»))))

p_2,3,4,0,1 = (sucf (sucf (zerof {2}))) — ((sucf (sucf (sucf (zerof {1})))) — ((sucf (sucf (sucf (sucf (zerof {0}))))) — (zerof {4} — ((sucf (zerof {3})) — «»))))

p_2,3,4,1,0 = (sucf (sucf (zerof {2}))) — ((sucf (sucf (sucf (zerof {1})))) — ((sucf (sucf (sucf (sucf (zerof {0}))))) — ((sucf (zerof {3})) — (zerof {4} — «»))))

p_2,4,0,1,3 = (sucf (sucf (zerof {2}))) — ((sucf (sucf (sucf (sucf (zerof {0}))))) — (zerof {4} — ((sucf (zerof {3})) — ((sucf (sucf (sucf (zerof {1})))) — «»))))

p_2,4,0,3,1 = (sucf (sucf (zerof {2}))) — ((sucf (sucf (sucf (sucf (zerof {0}))))) — (zerof {4} — ((sucf (sucf (sucf (zerof {1})))) — ((sucf (zerof {3})) — «»))))

p_2,4,1,0,3 = (sucf (sucf (zerof {2}))) — ((sucf (sucf (sucf (sucf (zerof {0}))))) — ((sucf (zerof {3})) — (zerof {4} — ((sucf (sucf (sucf (zerof {1})))) — «»))))

p_2,4,1,3,0 = (sucf (sucf (zerof {2}))) — ((sucf (sucf (sucf (sucf (zerof {0}))))) — ((sucf (zerof {3})) — ((sucf (sucf (sucf (zerof {1})))) — (zerof {4} — «»))))

p_2,4,3,0,1 = (sucf (sucf (zerof {2}))) — ((sucf (sucf (sucf (sucf (zerof {0}))))) — ((sucf (sucf (sucf (zerof {1})))) — (zerof {4} — ((sucf (zerof {3})) — «»))))

p_2,4,3,1,0 = (sucf (sucf (zerof {2}))) — ((sucf (sucf (sucf (sucf (zerof {0}))))) — ((sucf (sucf (sucf (zerof {1})))) — ((sucf (zerof {3})) — (zerof {4} — «»))))

p_3,0,1,2,4 = (sucf (sucf (sucf (zerof {1})))) — (zerof {4} — ((sucf (zerof {3})) — ((sucf (sucf (zerof {2}))) — ((sucf (sucf (sucf (sucf (zerof {0}))))) — «»))))

p_3,0,1,4,2 = (sucf (sucf (sucf (zerof {1})))) — (zerof {4} — ((sucf (zerof {3})) — ((sucf (sucf (sucf (sucf (zerof {0}))))) — ((sucf (sucf (zerof {2}))) — «»))))

p_3,0,2,1,4 = (sucf (sucf (sucf (zerof {1})))) — (zerof {4} — ((sucf (sucf (zerof {2}))) — ((sucf (zerof {3})) — ((sucf (sucf (sucf (sucf (zerof {0}))))) — «»))))

p_3,0,2,4,1 = (sucf (sucf (sucf (zerof {1})))) — (zerof {4} — ((sucf (sucf (zerof {2}))) — ((sucf (sucf (sucf (sucf (zerof {0}))))) — ((sucf (zerof {3})) — «»))))

p_3,0,4,1,2 = (sucf (sucf (sucf (zerof {1})))) — (zerof {4} — ((sucf (sucf (sucf (sucf (zerof {0}))))) — ((sucf (zerof {3})) — ((sucf (sucf (zerof {2}))) — «»))))

p_3,0,4,2,1 = (sucf (sucf (sucf (zerof {1})))) — (zerof {4} — ((sucf (sucf (sucf (sucf (zerof {0}))))) — ((sucf (sucf (zerof {2}))) — ((sucf (zerof {3})) — «»))))

p_3,1,0,2,4 = (sucf (sucf (sucf (zerof {1})))) — ((sucf (zerof {3})) — (zerof {4} — ((sucf (sucf (zerof {2}))) — ((sucf (sucf (sucf (sucf (zerof {0}))))) — «»))))

p_3,1,0,4,2 = (sucf (sucf (sucf (zerof {1})))) — ((sucf (zerof {3})) — (zerof {4} — ((sucf (sucf (sucf (sucf (zerof {0}))))) — ((sucf (sucf (zerof {2}))) — «»))))

p_3,1,2,0,4 = (sucf (sucf (sucf (zerof {1})))) — ((sucf (zerof {3})) — ((sucf (sucf (zerof {2}))) — (zerof {4} — ((sucf (sucf (sucf (sucf (zerof {0}))))) — «»))))

p_3,1,2,4,0 = (sucf (sucf (sucf (zerof {1})))) — ((sucf (zerof {3})) — ((sucf (sucf (zerof {2}))) — ((sucf (sucf (sucf (sucf (zerof {0}))))) — (zerof {4} — «»))))

p_3,1,4,0,2 = (sucf (sucf (sucf (zerof {1})))) — ((sucf (zerof {3})) — ((sucf (sucf (sucf (sucf (zerof {0}))))) — (zerof {4} — ((sucf (sucf (zerof {2}))) — «»))))

p_3,1,4,2,0 = (sucf (sucf (sucf (zerof {1})))) — ((sucf (zerof {3})) — ((sucf (sucf (sucf (sucf (zerof {0}))))) — ((sucf (sucf (zerof {2}))) — (zerof {4} — «»))))

p_3,2,0,1,4 = (sucf (sucf (sucf (zerof {1})))) — ((sucf (sucf (zerof {2}))) — (zerof {4} — ((sucf (zerof {3})) — ((sucf (sucf (sucf (sucf (zerof {0}))))) — «»))))

p_3,2,0,4,1 = (sucf (sucf (sucf (zerof {1})))) — ((sucf (sucf (zerof {2}))) — (zerof {4} — ((sucf (sucf (sucf (sucf (zerof {0}))))) — ((sucf (zerof {3})) — «»))))

p_3,2,1,0,4 = (sucf (sucf (sucf (zerof {1})))) — ((sucf (sucf (zerof {2}))) — ((sucf (zerof {3})) — (zerof {4} — ((sucf (sucf (sucf (sucf (zerof {0}))))) — «»))))

p_3,2,1,4,0 = (sucf (sucf (sucf (zerof {1})))) — ((sucf (sucf (zerof {2}))) — ((sucf (zerof {3})) — ((sucf (sucf (sucf (sucf (zerof {0}))))) — (zerof {4} — «»))))

p_3,2,4,0,1 = (sucf (sucf (sucf (zerof {1})))) — ((sucf (sucf (zerof {2}))) — ((sucf (sucf (sucf (sucf (zerof {0}))))) — (zerof {4} — ((sucf (zerof {3})) — «»))))

p_3,2,4,1,0 = (sucf (sucf (sucf (zerof {1})))) — ((sucf (sucf (zerof {2}))) — ((sucf (sucf (sucf (sucf (zerof {0}))))) — ((sucf (zerof {3})) — (zerof {4} — «»))))

p_3,4,0,1,2 = (sucf (sucf (sucf (zerof {1})))) — ((sucf (sucf (sucf (sucf (zerof {0}))))) — (zerof {4} — ((sucf (zerof {3})) — ((sucf (sucf (zerof {2}))) — «»))))

p_3,4,0,2,1 = (sucf (sucf (sucf (zerof {1})))) — ((sucf (sucf (sucf (sucf (zerof {0}))))) — (zerof {4} — ((sucf (sucf (zerof {2}))) — ((sucf (zerof {3})) — «»))))

p_3,4,1,0,2 = (sucf (sucf (sucf (zerof {1})))) — ((sucf (sucf (sucf (sucf (zerof {0}))))) — ((sucf (zerof {3})) — (zerof {4} — ((sucf (sucf (zerof {2}))) — «»))))

p_3,4,1,2,0 = (sucf (sucf (sucf (zerof {1})))) — ((sucf (sucf (sucf (sucf (zerof {0}))))) — ((sucf (zerof {3})) — ((sucf (sucf (zerof {2}))) — (zerof {4} — «»))))

p_3,4,2,0,1 = (sucf (sucf (sucf (zerof {1})))) — ((sucf (sucf (sucf (sucf (zerof {0}))))) — ((sucf (sucf (zerof {2}))) — (zerof {4} — ((sucf (zerof {3})) — «»))))

p_3,4,2,1,0 = (sucf (sucf (sucf (zerof {1})))) — ((sucf (sucf (sucf (sucf (zerof {0}))))) — ((sucf (sucf (zerof {2}))) — ((sucf (zerof {3})) — (zerof {4} — «»))))

p_4,0,1,2,3 = (sucf (sucf (sucf (sucf (zerof {0}))))) — (zerof {4} — ((sucf (zerof {3})) — ((sucf (sucf (zerof {2}))) — ((sucf (sucf (sucf (zerof {1})))) — «»))))

p_4,0,1,3,2 = (sucf (sucf (sucf (sucf (zerof {0}))))) — (zerof {4} — ((sucf (zerof {3})) — ((sucf (sucf (sucf (zerof {1})))) — ((sucf (sucf (zerof {2}))) — «»))))

p_4,0,2,1,3 = (sucf (sucf (sucf (sucf (zerof {0}))))) — (zerof {4} — ((sucf (sucf (zerof {2}))) — ((sucf (zerof {3})) — ((sucf (sucf (sucf (zerof {1})))) — «»))))

p_4,0,2,3,1 = (sucf (sucf (sucf (sucf (zerof {0}))))) — (zerof {4} — ((sucf (sucf (zerof {2}))) — ((sucf (sucf (sucf (zerof {1})))) — ((sucf (zerof {3})) — «»))))

p_4,0,3,1,2 = (sucf (sucf (sucf (sucf (zerof {0}))))) — (zerof {4} — ((sucf (sucf (sucf (zerof {1})))) — ((sucf (zerof {3})) — ((sucf (sucf (zerof {2}))) — «»))))

p_4,0,3,2,1 = (sucf (sucf (sucf (sucf (zerof {0}))))) — (zerof {4} — ((sucf (sucf (sucf (zerof {1})))) — ((sucf (sucf (zerof {2}))) — ((sucf (zerof {3})) — «»))))

p_4,1,0,2,3 = (sucf (sucf (sucf (sucf (zerof {0}))))) — ((sucf (zerof {3})) — (zerof {4} — ((sucf (sucf (zerof {2}))) — ((sucf (sucf (sucf (zerof {1})))) — «»))))

p_4,1,0,3,2 = (sucf (sucf (sucf (sucf (zerof {0}))))) — ((sucf (zerof {3})) — (zerof {4} — ((sucf (sucf (sucf (zerof {1})))) — ((sucf (sucf (zerof {2}))) — «»))))

p_4,1,2,0,3 = (sucf (sucf (sucf (sucf (zerof {0}))))) — ((sucf (zerof {3})) — ((sucf (sucf (zerof {2}))) — (zerof {4} — ((sucf (sucf (sucf (zerof {1})))) — «»))))

p_4,1,2,3,0 = (sucf (sucf (sucf (sucf (zerof {0}))))) — ((sucf (zerof {3})) — ((sucf (sucf (zerof {2}))) — ((sucf (sucf (sucf (zerof {1})))) — (zerof {4} — «»))))

p_4,1,3,0,2 = (sucf (sucf (sucf (sucf (zerof {0}))))) — ((sucf (zerof {3})) — ((sucf (sucf (sucf (zerof {1})))) — (zerof {4} — ((sucf (sucf (zerof {2}))) — «»))))

p_4,1,3,2,0 = (sucf (sucf (sucf (sucf (zerof {0}))))) — ((sucf (zerof {3})) — ((sucf (sucf (sucf (zerof {1})))) — ((sucf (sucf (zerof {2}))) — (zerof {4} — «»))))

p_4,2,0,1,3 = (sucf (sucf (sucf (sucf (zerof {0}))))) — ((sucf (sucf (zerof {2}))) — (zerof {4} — ((sucf (zerof {3})) — ((sucf (sucf (sucf (zerof {1})))) — «»))))

p_4,2,0,3,1 = (sucf (sucf (sucf (sucf (zerof {0}))))) — ((sucf (sucf (zerof {2}))) — (zerof {4} — ((sucf (sucf (sucf (zerof {1})))) — ((sucf (zerof {3})) — «»))))

p_4,2,1,0,3 = (sucf (sucf (sucf (sucf (zerof {0}))))) — ((sucf (sucf (zerof {2}))) — ((sucf (zerof {3})) — (zerof {4} — ((sucf (sucf (sucf (zerof {1})))) — «»))))

p_4,2,1,3,0 = (sucf (sucf (sucf (sucf (zerof {0}))))) — ((sucf (sucf (zerof {2}))) — ((sucf (zerof {3})) — ((sucf (sucf (sucf (zerof {1})))) — (zerof {4} — «»))))

p_4,2,3,0,1 = (sucf (sucf (sucf (sucf (zerof {0}))))) — ((sucf (sucf (zerof {2}))) — ((sucf (sucf (sucf (zerof {1})))) — (zerof {4} — ((sucf (zerof {3})) — «»))))

p_4,2,3,1,0 = (sucf (sucf (sucf (sucf (zerof {0}))))) — ((sucf (sucf (zerof {2}))) — ((sucf (sucf (sucf (zerof {1})))) — ((sucf (zerof {3})) — (zerof {4} — «»))))

p_4,3,0,1,2 = (sucf (sucf (sucf (sucf (zerof {0}))))) — ((sucf (sucf (sucf (zerof {1})))) — (zerof {4} — ((sucf (zerof {3})) — ((sucf (sucf (zerof {2}))) — «»))))

p_4,3,0,2,1 = (sucf (sucf (sucf (sucf (zerof {0}))))) — ((sucf (sucf (sucf (zerof {1})))) — (zerof {4} — ((sucf (sucf (zerof {2}))) — ((sucf (zerof {3})) — «»))))

p_4,3,1,0,2 = (sucf (sucf (sucf (sucf (zerof {0}))))) — ((sucf (sucf (sucf (zerof {1})))) — ((sucf (zerof {3})) — (zerof {4} — ((sucf (sucf (zerof {2}))) — «»))))

p_4,3,1,2,0 = (sucf (sucf (sucf (sucf (zerof {0}))))) — ((sucf (sucf (sucf (zerof {1})))) — ((sucf (zerof {3})) — ((sucf (sucf (zerof {2}))) — (zerof {4} — «»))))

p_4,3,2,0,1 = (sucf (sucf (sucf (sucf (zerof {0}))))) — ((sucf (sucf (sucf (zerof {1})))) — ((sucf (sucf (zerof {2}))) — (zerof {4} — ((sucf (zerof {3})) — «»))))

p_4,3,2,1,0 = (sucf (sucf (sucf (sucf (zerof {0}))))) — ((sucf (sucf (sucf (zerof {1})))) — ((sucf (sucf (zerof {2}))) — ((sucf (zerof {3})) — (zerof {4} — «»))))

lis = p_0,1,2,3,4 ∷ p_0,1,2,4,3 ∷ p_0,1,3,2,4 ∷ p_0,1,3,4,2 ∷ p_0,1,4,2,3 ∷ p_0,1,4,3,2 ∷ p_0,2,1,3,4 ∷ p_0,2,1,4,3 ∷ p_0,2,3,1,4 ∷ p_0,2,3,4,1 ∷ p_0,2,4,1,3 ∷ p_0,2,4,3,1 ∷ p_0,3,1,2,4 ∷ p_0,3,1,4,2 ∷ p_0,3,2,1,4 ∷ p_0,3,2,4,1 ∷ p_0,3,4,1,2 ∷ p_0,3,4,2,1 ∷ p_0,4,1,2,3 ∷ p_0,4,1,3,2 ∷ p_0,4,2,1,3 ∷ p_0,4,2,3,1 ∷ p_0,4,3,1,2 ∷ p_0,4,3,2,1 ∷ p_1,0,2,3,4 ∷ p_1,0,2,4,3 ∷ p_1,0,3,2,4 ∷ p_1,0,3,4,2 ∷ p_1,0,4,2,3 ∷ p_1,0,4,3,2 ∷ p_1,2,0,3,4 ∷ p_1,2,0,4,3 ∷ p_1,2,3,0,4 ∷ p_1,2,3,4,0 ∷ p_1,2,4,0,3 ∷ p_1,2,4,3,0 ∷ p_1,3,0,2,4 ∷ p_1,3,0,4,2 ∷ p_1,3,2,0,4 ∷ p_1,3,2,4,0 ∷ p_1,3,4,0,2 ∷ p_1,3,4,2,0 ∷ p_1,4,0,2,3 ∷ p_1,4,0,3,2 ∷ p_1,4,2,0,3 ∷ p_1,4,2,3,0 ∷ p_1,4,3,0,2 ∷ p_1,4,3,2,0 ∷ p_2,0,1,3,4 ∷ p_2,0,1,4,3 ∷ p_2,0,3,1,4 ∷ p_2,0,3,4,1 ∷ p_2,0,4,1,3 ∷ p_2,0,4,3,1 ∷ p_2,1,0,3,4 ∷ p_2,1,0,4,3 ∷ p_2,1,3,0,4 ∷ p_2,1,3,4,0 ∷ p_2,1,4,0,3 ∷ p_2,1,4,3,0 ∷ p_2,3,0,1,4 ∷ p_2,3,0,4,1 ∷ p_2,3,1,0,4 ∷ p_2,3,1,4,0 ∷ p_2,3,4,0,1 ∷ p_2,3,4,1,0 ∷ p_2,4,0,1,3 ∷ p_2,4,0,3,1 ∷ p_2,4,1,0,3 ∷ p_2,4,1,3,0 ∷ p_2,4,3,0,1 ∷ p_2,4,3,1,0 ∷ p_3,0,1,2,4 ∷ p_3,0,1,4,2 ∷ p_3,0,2,1,4 ∷ p_3,0,2,4,1 ∷ p_3,0,4,1,2 ∷ p_3,0,4,2,1 ∷ p_3,1,0,2,4 ∷ p_3,1,0,4,2 ∷ p_3,1,2,0,4 ∷ p_3,1,2,4,0 ∷ p_3,1,4,0,2 ∷ p_3,1,4,2,0 ∷ p_3,2,0,1,4 ∷ p_3,2,0,4,1 ∷ p_3,2,1,0,4 ∷ p_3,2,1,4,0 ∷ p_3,2,4,0,1 ∷ p_3,2,4,1,0 ∷ p_3,4,0,1,2 ∷ p_3,4,0,2,1 ∷ p_3,4,1,0,2 ∷ p_3,4,1,2,0 ∷ p_3,4,2,0,1 ∷ p_3,4,2,1,0 ∷ p_4,0,1,2,3 ∷ p_4,0,1,3,2 ∷ p_4,0,2,1,3 ∷ p_4,0,2,3,1 ∷ p_4,0,3,1,2 ∷ p_4,0,3,2,1 ∷ p_4,1,0,2,3 ∷ p_4,1,0,3,2 ∷ p_4,1,2,0,3 ∷ p_4,1,2,3,0 ∷ p_4,1,3,0,2 ∷ p_4,1,3,2,0 ∷ p_4,2,0,1,3 ∷ p_4,2,0,3,1 ∷ p_4,2,1,0,3 ∷ p_4,2,1,3,0 ∷ p_4,2,3,0,1 ∷ p_4,2,3,1,0 ∷ p_4,3,0,1,2 ∷ p_4,3,0,2,1 ∷ p_4,3,1,0,2 ∷ p_4,3,1,2,0 ∷ p_4,3,2,0,1 ∷ p_4,3,2,1,0 ∷ []

----------------
-- Алгоритм сортировки
----------------

autoalg : Alg lis
autoalg = node (zerof) (sucf (zerof)) prfNoteq5--0,1 
        (node (zerof) (sucf (sucf (zerof))) prfNoteq5--0,2 
                (node (zerof) (sucf (sucf (sucf (zerof)))) prfNoteq5--0,3 
                        (node (zerof) (sucf (sucf (sucf (sucf (zerof))))) prfNoteq5--0,4 
                                (node (sucf (zerof)) (sucf (sucf (zerof))) prfNoteq5--1,2 
                                        (node (sucf (zerof)) (sucf (sucf (sucf (zerof)))) prfNoteq5--1,3 
                                                (node (sucf (zerof)) (sucf (sucf (sucf (sucf (zerof))))) prfNoteq5--1,4 
                                                        (node (sucf (sucf (zerof))) (sucf (sucf (sucf (zerof)))) prfNoteq5--2,3 
                                                                (node (sucf (sucf (zerof))) (sucf (sucf (sucf (sucf (zerof))))) prfNoteq5--2,4 
                                                                        (node (sucf (sucf (sucf (zerof)))) (sucf (sucf (sucf (sucf (zerof))))) prfNoteq5--3,4 
                                                                                (leaf p_0,1,2,3,4)
                                                                                (leaf p_0,1,2,4,3))
                                                                        (leaf p_0,1,3,4,2))
                                                                (node (sucf (sucf (zerof))) (sucf (sucf (sucf (sucf (zerof))))) prfNoteq5--2,4 
                                                                        (leaf p_0,1,3,2,4)
                                                                        (node (sucf (sucf (sucf (zerof)))) (sucf (sucf (sucf (sucf (zerof))))) prfNoteq5--3,4 
                                                                                (leaf p_0,1,4,2,3)
                                                                                (leaf p_0,1,4,3,2))))
                                                        (node (sucf (sucf (zerof))) (sucf (sucf (sucf (zerof)))) prfNoteq5--2,3 
                                                                (leaf p_0,2,3,4,1)
                                                                (leaf p_0,2,4,3,1)))
                                                (node (sucf (zerof)) (sucf (sucf (sucf (sucf (zerof))))) prfNoteq5--1,4 
                                                        (node (sucf (sucf (zerof))) (sucf (sucf (sucf (sucf (zerof))))) prfNoteq5--2,4 
                                                                (leaf p_0,2,3,1,4)
                                                                (leaf p_0,2,4,1,3))
                                                        (node (sucf (sucf (sucf (zerof)))) (sucf (sucf (sucf (sucf (zerof))))) prfNoteq5--3,4 
                                                                (leaf p_0,3,4,1,2)
                                                                (leaf p_0,3,4,2,1))))
                                        (node (sucf (zerof)) (sucf (sucf (sucf (zerof)))) prfNoteq5--1,3 
                                                (node (sucf (zerof)) (sucf (sucf (sucf (sucf (zerof))))) prfNoteq5--1,4 
                                                        (node (sucf (sucf (sucf (zerof)))) (sucf (sucf (sucf (sucf (zerof))))) prfNoteq5--3,4 
                                                                (leaf p_0,2,1,3,4)
                                                                (leaf p_0,2,1,4,3))
                                                        (node (sucf (sucf (zerof))) (sucf (sucf (sucf (sucf (zerof))))) prfNoteq5--2,4 
                                                                (leaf p_0,3,1,4,2)
                                                                (leaf p_0,3,2,4,1)))
                                                (node (sucf (zerof)) (sucf (sucf (sucf (sucf (zerof))))) prfNoteq5--1,4 
                                                        (node (sucf (sucf (zerof))) (sucf (sucf (sucf (zerof)))) prfNoteq5--2,3 
                                                                (leaf p_0,3,1,2,4)
                                                                (leaf p_0,3,2,1,4))
                                                        (node (sucf (sucf (zerof))) (sucf (sucf (sucf (zerof)))) prfNoteq5--2,3 
                                                                (node (sucf (sucf (zerof))) (sucf (sucf (sucf (sucf (zerof))))) prfNoteq5--2,4 
                                                                        (node (sucf (sucf (sucf (zerof)))) (sucf (sucf (sucf (sucf (zerof))))) prfNoteq5--3,4 
                                                                                (leaf p_0,4,1,2,3)
                                                                                (leaf p_0,4,1,3,2))
                                                                        (leaf p_0,4,2,3,1))
                                                                (node (sucf (sucf (zerof))) (sucf (sucf (sucf (sucf (zerof))))) prfNoteq5--2,4 
                                                                        (leaf p_0,4,2,1,3)
                                                                        (node (sucf (sucf (sucf (zerof)))) (sucf (sucf (sucf (sucf (zerof))))) prfNoteq5--3,4 
                                                                                (leaf p_0,4,3,1,2)
                                                                                (leaf p_0,4,3,2,1)))))))
                                (node (sucf (zerof)) (sucf (sucf (zerof))) prfNoteq5--1,2 
                                        (node (sucf (zerof)) (sucf (sucf (sucf (zerof)))) prfNoteq5--1,3 
                                                (node (sucf (sucf (zerof))) (sucf (sucf (sucf (zerof)))) prfNoteq5--2,3 
                                                        (leaf p_1,2,3,4,0)
                                                        (leaf p_1,2,4,3,0))
                                                (leaf p_1,3,4,2,0))
                                        (node (sucf (zerof)) (sucf (sucf (sucf (zerof)))) prfNoteq5--1,3 
                                                (leaf p_1,3,2,4,0)
                                                (node (sucf (sucf (zerof))) (sucf (sucf (sucf (zerof)))) prfNoteq5--2,3 
                                                        (leaf p_1,4,2,3,0)
                                                        (leaf p_1,4,3,2,0)))))
                        (node (zerof) (sucf (sucf (sucf (sucf (zerof))))) prfNoteq5--0,4 
                                (node (sucf (zerof)) (sucf (sucf (zerof))) prfNoteq5--1,2 
                                        (node (sucf (zerof)) (sucf (sucf (sucf (sucf (zerof))))) prfNoteq5--1,4 
                                                (node (sucf (sucf (zerof))) (sucf (sucf (sucf (sucf (zerof))))) prfNoteq5--2,4 
                                                        (leaf p_1,2,3,0,4)
                                                        (leaf p_1,2,4,0,3))
                                                (leaf p_1,3,4,0,2))
                                        (node (sucf (zerof)) (sucf (sucf (sucf (sucf (zerof))))) prfNoteq5--1,4 
                                                (leaf p_1,3,2,0,4)
                                                (node (sucf (sucf (zerof))) (sucf (sucf (sucf (sucf (zerof))))) prfNoteq5--2,4 
                                                        (leaf p_1,4,2,0,3)
                                                        (leaf p_1,4,3,0,2))))
                                (node (sucf (zerof)) (sucf (sucf (zerof))) prfNoteq5--1,2 
                                        (node (sucf (sucf (sucf (zerof)))) (sucf (sucf (sucf (sucf (zerof))))) prfNoteq5--3,4 
                                                (leaf p_2,3,4,0,1)
                                                (leaf p_2,3,4,1,0))
                                        (node (sucf (sucf (sucf (zerof)))) (sucf (sucf (sucf (sucf (zerof))))) prfNoteq5--3,4 
                                                (leaf p_2,4,3,0,1)
                                                (leaf p_2,4,3,1,0)))))
                (node (zerof) (sucf (sucf (sucf (zerof)))) prfNoteq5--0,3 
                        (node (zerof) (sucf (sucf (sucf (sucf (zerof))))) prfNoteq5--0,4 
                                (node (sucf (zerof)) (sucf (sucf (sucf (zerof)))) prfNoteq5--1,3 
                                        (node (sucf (zerof)) (sucf (sucf (sucf (sucf (zerof))))) prfNoteq5--1,4 
                                                (node (sucf (sucf (sucf (zerof)))) (sucf (sucf (sucf (sucf (zerof))))) prfNoteq5--3,4 
                                                        (leaf p_1,2,0,3,4)
                                                        (leaf p_1,2,0,4,3))
                                                (leaf p_1,3,0,4,2))
                                        (node (sucf (zerof)) (sucf (sucf (sucf (sucf (zerof))))) prfNoteq5--1,4 
                                                (leaf p_1,3,0,2,4)
                                                (node (sucf (sucf (sucf (zerof)))) (sucf (sucf (sucf (sucf (zerof))))) prfNoteq5--3,4 
                                                        (leaf p_1,4,0,2,3)
                                                        (leaf p_1,4,0,3,2))))
                                (node (sucf (zerof)) (sucf (sucf (sucf (zerof)))) prfNoteq5--1,3 
                                        (node (sucf (sucf (zerof))) (sucf (sucf (sucf (sucf (zerof))))) prfNoteq5--2,4 
                                                (leaf p_2,3,0,4,1)
                                                (leaf p_2,3,1,4,0))
                                        (node (sucf (sucf (zerof))) (sucf (sucf (sucf (sucf (zerof))))) prfNoteq5--2,4 
                                                (leaf p_2,4,0,3,1)
                                                (leaf p_2,4,1,3,0))))
                        (node (zerof) (sucf (sucf (sucf (sucf (zerof))))) prfNoteq5--0,4 
                                (node (sucf (zerof)) (sucf (sucf (sucf (sucf (zerof))))) prfNoteq5--1,4 
                                        (node (sucf (sucf (zerof))) (sucf (sucf (sucf (zerof)))) prfNoteq5--2,3 
                                                (leaf p_2,3,0,1,4)
                                                (leaf p_2,3,1,0,4))
                                        (node (sucf (sucf (zerof))) (sucf (sucf (sucf (zerof)))) prfNoteq5--2,3 
                                                (leaf p_2,4,0,1,3)
                                                (leaf p_2,4,1,0,3)))
                                (node (sucf (sucf (zerof))) (sucf (sucf (sucf (zerof)))) prfNoteq5--2,3 
                                        (node (sucf (sucf (zerof))) (sucf (sucf (sucf (sucf (zerof))))) prfNoteq5--2,4 
                                                (node (sucf (sucf (sucf (zerof)))) (sucf (sucf (sucf (sucf (zerof))))) prfNoteq5--3,4 
                                                        (leaf p_3,4,0,1,2)
                                                        (leaf p_3,4,0,2,1))
                                                (leaf p_3,4,1,2,0))
                                        (node (sucf (sucf (zerof))) (sucf (sucf (sucf (sucf (zerof))))) prfNoteq5--2,4 
                                                (leaf p_3,4,1,0,2)
                                                (node (sucf (sucf (sucf (zerof)))) (sucf (sucf (sucf (sucf (zerof))))) prfNoteq5--3,4 
                                                        (leaf p_3,4,2,0,1)
                                                        (leaf p_3,4,2,1,0)))))))
        (node (zerof) (sucf (sucf (zerof))) prfNoteq5--0,2 
                (node (zerof) (sucf (sucf (sucf (zerof)))) prfNoteq5--0,3 
                        (node (zerof) (sucf (sucf (sucf (sucf (zerof))))) prfNoteq5--0,4 
                                (node (sucf (sucf (zerof))) (sucf (sucf (sucf (zerof)))) prfNoteq5--2,3 
                                        (node (sucf (sucf (zerof))) (sucf (sucf (sucf (sucf (zerof))))) prfNoteq5--2,4 
                                                (node (sucf (sucf (sucf (zerof)))) (sucf (sucf (sucf (sucf (zerof))))) prfNoteq5--3,4 
                                                        (leaf p_1,0,2,3,4)
                                                        (leaf p_1,0,2,4,3))
                                                (leaf p_1,0,3,4,2))
                                        (node (sucf (sucf (zerof))) (sucf (sucf (sucf (sucf (zerof))))) prfNoteq5--2,4 
                                                (leaf p_1,0,3,2,4)
                                                (node (sucf (sucf (sucf (zerof)))) (sucf (sucf (sucf (sucf (zerof))))) prfNoteq5--3,4 
                                                        (leaf p_1,0,4,2,3)
                                                        (leaf p_1,0,4,3,2))))
                                (node (sucf (zerof)) (sucf (sucf (sucf (sucf (zerof))))) prfNoteq5--1,4 
                                        (node (sucf (sucf (zerof))) (sucf (sucf (sucf (zerof)))) prfNoteq5--2,3 
                                                (leaf p_2,0,3,4,1)
                                                (leaf p_2,0,4,3,1))
                                        (node (sucf (sucf (zerof))) (sucf (sucf (sucf (zerof)))) prfNoteq5--2,3 
                                                (leaf p_2,1,3,4,0)
                                                (leaf p_2,1,4,3,0))))
                        (node (zerof) (sucf (sucf (sucf (sucf (zerof))))) prfNoteq5--0,4 
                                (node (sucf (zerof)) (sucf (sucf (sucf (zerof)))) prfNoteq5--1,3 
                                        (node (sucf (sucf (zerof))) (sucf (sucf (sucf (sucf (zerof))))) prfNoteq5--2,4 
                                                (leaf p_2,0,3,1,4)
                                                (leaf p_2,0,4,1,3))
                                        (node (sucf (sucf (zerof))) (sucf (sucf (sucf (sucf (zerof))))) prfNoteq5--2,4 
                                                (leaf p_2,1,3,0,4)
                                                (leaf p_2,1,4,0,3)))
                                (node (sucf (zerof)) (sucf (sucf (sucf (zerof)))) prfNoteq5--1,3 
                                        (node (sucf (zerof)) (sucf (sucf (sucf (sucf (zerof))))) prfNoteq5--1,4 
                                                (node (sucf (sucf (sucf (zerof)))) (sucf (sucf (sucf (sucf (zerof))))) prfNoteq5--3,4 
                                                        (leaf p_3,0,4,1,2)
                                                        (leaf p_3,0,4,2,1))
                                                (leaf p_3,1,4,2,0))
                                        (node (sucf (zerof)) (sucf (sucf (sucf (sucf (zerof))))) prfNoteq5--1,4 
                                                (leaf p_3,1,4,0,2)
                                                (node (sucf (sucf (sucf (zerof)))) (sucf (sucf (sucf (sucf (zerof))))) prfNoteq5--3,4 
                                                        (leaf p_3,2,4,0,1)
                                                        (leaf p_3,2,4,1,0))))))
                (node (zerof) (sucf (sucf (sucf (zerof)))) prfNoteq5--0,3 
                        (node (zerof) (sucf (sucf (sucf (sucf (zerof))))) prfNoteq5--0,4 
                                (node (sucf (zerof)) (sucf (sucf (zerof))) prfNoteq5--1,2 
                                        (node (sucf (sucf (sucf (zerof)))) (sucf (sucf (sucf (sucf (zerof))))) prfNoteq5--3,4 
                                                (leaf p_2,0,1,3,4)
                                                (leaf p_2,0,1,4,3))
                                        (node (sucf (sucf (sucf (zerof)))) (sucf (sucf (sucf (sucf (zerof))))) prfNoteq5--3,4 
                                                (leaf p_2,1,0,3,4)
                                                (leaf p_2,1,0,4,3)))
                                (node (sucf (zerof)) (sucf (sucf (zerof))) prfNoteq5--1,2 
                                        (node (sucf (zerof)) (sucf (sucf (sucf (sucf (zerof))))) prfNoteq5--1,4 
                                                (node (sucf (sucf (zerof))) (sucf (sucf (sucf (sucf (zerof))))) prfNoteq5--2,4 
                                                        (leaf p_3,0,1,4,2)
                                                        (leaf p_3,0,2,4,1))
                                                (leaf p_3,1,2,4,0))
                                        (node (sucf (zerof)) (sucf (sucf (sucf (sucf (zerof))))) prfNoteq5--1,4 
                                                (leaf p_3,1,0,4,2)
                                                (node (sucf (sucf (zerof))) (sucf (sucf (sucf (sucf (zerof))))) prfNoteq5--2,4 
                                                        (leaf p_3,2,0,4,1)
                                                        (leaf p_3,2,1,4,0)))))
                        (node (zerof) (sucf (sucf (sucf (sucf (zerof))))) prfNoteq5--0,4 
                                (node (sucf (zerof)) (sucf (sucf (zerof))) prfNoteq5--1,2 
                                        (node (sucf (zerof)) (sucf (sucf (sucf (zerof)))) prfNoteq5--1,3 
                                                (node (sucf (sucf (zerof))) (sucf (sucf (sucf (zerof)))) prfNoteq5--2,3 
                                                        (leaf p_3,0,1,2,4)
                                                        (leaf p_3,0,2,1,4))
                                                (leaf p_3,1,2,0,4))
                                        (node (sucf (zerof)) (sucf (sucf (sucf (zerof)))) prfNoteq5--1,3 
                                                (leaf p_3,1,0,2,4)
                                                (node (sucf (sucf (zerof))) (sucf (sucf (sucf (zerof)))) prfNoteq5--2,3 
                                                        (leaf p_3,2,0,1,4)
                                                        (leaf p_3,2,1,0,4))))
                                (node (sucf (zerof)) (sucf (sucf (zerof))) prfNoteq5--1,2 
                                        (node (sucf (zerof)) (sucf (sucf (sucf (zerof)))) prfNoteq5--1,3 
                                                (node (sucf (zerof)) (sucf (sucf (sucf (sucf (zerof))))) prfNoteq5--1,4 
                                                        (node (sucf (sucf (zerof))) (sucf (sucf (sucf (zerof)))) prfNoteq5--2,3 
                                                                (node (sucf (sucf (zerof))) (sucf (sucf (sucf (sucf (zerof))))) prfNoteq5--2,4 
                                                                        (node (sucf (sucf (sucf (zerof)))) (sucf (sucf (sucf (sucf (zerof))))) prfNoteq5--3,4 
                                                                                (leaf p_4,0,1,2,3)
                                                                                (leaf p_4,0,1,3,2))
                                                                        (leaf p_4,0,2,3,1))
                                                                (node (sucf (sucf (zerof))) (sucf (sucf (sucf (sucf (zerof))))) prfNoteq5--2,4 
                                                                        (leaf p_4,0,2,1,3)
                                                                        (node (sucf (sucf (sucf (zerof)))) (sucf (sucf (sucf (sucf (zerof))))) prfNoteq5--3,4 
                                                                                (leaf p_4,0,3,1,2)
                                                                                (leaf p_4,0,3,2,1))))
                                                        (node (sucf (sucf (zerof))) (sucf (sucf (sucf (zerof)))) prfNoteq5--2,3 
                                                                (leaf p_4,1,2,3,0)
                                                                (leaf p_4,1,3,2,0)))
                                                (node (sucf (zerof)) (sucf (sucf (sucf (sucf (zerof))))) prfNoteq5--1,4 
                                                        (node (sucf (sucf (zerof))) (sucf (sucf (sucf (sucf (zerof))))) prfNoteq5--2,4 
                                                                (leaf p_4,1,2,0,3)
                                                                (leaf p_4,1,3,0,2))
                                                        (node (sucf (sucf (sucf (zerof)))) (sucf (sucf (sucf (sucf (zerof))))) prfNoteq5--3,4 
                                                                (leaf p_4,2,3,0,1)
                                                                (leaf p_4,2,3,1,0))))
                                        (node (sucf (zerof)) (sucf (sucf (sucf (zerof)))) prfNoteq5--1,3 
                                                (node (sucf (zerof)) (sucf (sucf (sucf (sucf (zerof))))) prfNoteq5--1,4 
                                                        (node (sucf (sucf (sucf (zerof)))) (sucf (sucf (sucf (sucf (zerof))))) prfNoteq5--3,4 
                                                                (leaf p_4,1,0,2,3)
                                                                (leaf p_4,1,0,3,2))
                                                        (node (sucf (sucf (zerof))) (sucf (sucf (sucf (sucf (zerof))))) prfNoteq5--2,4 
                                                                (leaf p_4,2,0,3,1)
                                                                (leaf p_4,2,1,3,0)))
                                                (node (sucf (zerof)) (sucf (sucf (sucf (sucf (zerof))))) prfNoteq5--1,4 
                                                        (node (sucf (sucf (zerof))) (sucf (sucf (sucf (zerof)))) prfNoteq5--2,3 
                                                                (leaf p_4,2,0,1,3)
                                                                (leaf p_4,2,1,0,3))
                                                        (node (sucf (sucf (zerof))) (sucf (sucf (sucf (zerof)))) prfNoteq5--2,3 
                                                                (node (sucf (sucf (zerof))) (sucf (sucf (sucf (sucf (zerof))))) prfNoteq5--2,4 
                                                                        (node (sucf (sucf (sucf (zerof)))) (sucf (sucf (sucf (sucf (zerof))))) prfNoteq5--3,4 
                                                                                (leaf p_4,3,0,1,2)
                                                                                (leaf p_4,3,0,2,1))
                                                                        (leaf p_4,3,1,2,0))
                                                                (node (sucf (sucf (zerof))) (sucf (sucf (sucf (sucf (zerof))))) prfNoteq5--2,4 
                                                                        (leaf p_4,3,1,0,2)
                                                                        (node (sucf (sucf (sucf (zerof)))) (sucf (sucf (sucf (sucf (zerof))))) prfNoteq5--3,4 
                                                                                (leaf p_4,3,2,0,1)
                                                                                (leaf p_4,3,2,1,0))))))))))
