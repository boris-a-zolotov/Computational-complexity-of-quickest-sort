----------------
-- Аномальный список — длины 30,
-- но не сортирующийся за 5 шагов.
----------------

module anomal_jumbo_list where

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
-- Все элементы типа Fin 6 попарно различны.
----------------

prfNoteq6--0,1 : zerof {5} ≢ sucf (zerof {4})
prfNoteq6--0,1 = λ P → noteq
  (toℕ (zerof {5}))
  (toℕ (sucf (zerof {4})))
  (s≤s z≤n)
  (eq_cong toℕ P)

prfNoteq6--0,2 : zerof {5} ≢ sucf (sucf (zerof {3}))
prfNoteq6--0,2 = λ P → noteq
  (toℕ (zerof {5}))
  (toℕ (sucf (sucf (zerof {3}))))
  (s≤s z≤n)
  (eq_cong toℕ P)

prfNoteq6--0,3 : zerof {5} ≢ sucf (sucf (sucf (zerof {2})))
prfNoteq6--0,3 = λ P → noteq
  (toℕ (zerof {5}))
  (toℕ (sucf (sucf (sucf (zerof {2})))))
  (s≤s z≤n)
  (eq_cong toℕ P)

prfNoteq6--0,4 : zerof {5} ≢ sucf (sucf (sucf (sucf (zerof {1}))))
prfNoteq6--0,4 = λ P → noteq
  (toℕ (zerof {5}))
  (toℕ (sucf (sucf (sucf (sucf (zerof {1}))))))
  (s≤s z≤n)
  (eq_cong toℕ P)

prfNoteq6--0,5 : zerof {5} ≢ sucf (sucf (sucf (sucf (sucf (zerof {0})))))
prfNoteq6--0,5 = λ P → noteq
  (toℕ (zerof {5}))
  (toℕ (sucf (sucf (sucf (sucf (sucf (zerof {0})))))))
  (s≤s z≤n)
  (eq_cong toℕ P)

prfNoteq6--1,2 : sucf (zerof {4}) ≢ sucf (sucf (zerof {3}))
prfNoteq6--1,2 = λ P → noteq
  (toℕ (sucf (zerof {4})))
  (toℕ (sucf (sucf (zerof {3}))))
  (s≤s (s≤s z≤n))
  (eq_cong toℕ P)

prfNoteq6--1,3 : sucf (zerof {4}) ≢ sucf (sucf (sucf (zerof {2})))
prfNoteq6--1,3 = λ P → noteq
  (toℕ (sucf (zerof {4})))
  (toℕ (sucf (sucf (sucf (zerof {2})))))
  (s≤s (s≤s z≤n))
  (eq_cong toℕ P)

prfNoteq6--1,4 : sucf (zerof {4}) ≢ sucf (sucf (sucf (sucf (zerof {1}))))
prfNoteq6--1,4 = λ P → noteq
  (toℕ (sucf (zerof {4})))
  (toℕ (sucf (sucf (sucf (sucf (zerof {1}))))))
  (s≤s (s≤s z≤n))
  (eq_cong toℕ P)

prfNoteq6--1,5 : sucf (zerof {4}) ≢ sucf (sucf (sucf (sucf (sucf (zerof {0})))))
prfNoteq6--1,5 = λ P → noteq
  (toℕ (sucf (zerof {4})))
  (toℕ (sucf (sucf (sucf (sucf (sucf (zerof {0})))))))
  (s≤s (s≤s z≤n))
  (eq_cong toℕ P)

prfNoteq6--2,3 : sucf (sucf (zerof {3})) ≢ sucf (sucf (sucf (zerof {2})))
prfNoteq6--2,3 = λ P → noteq
  (toℕ (sucf (sucf (zerof {3}))))
  (toℕ (sucf (sucf (sucf (zerof {2})))))
  (s≤s (s≤s (s≤s z≤n)))
  (eq_cong toℕ P)

prfNoteq6--2,4 : sucf (sucf (zerof {3})) ≢ sucf (sucf (sucf (sucf (zerof {1}))))
prfNoteq6--2,4 = λ P → noteq
  (toℕ (sucf (sucf (zerof {3}))))
  (toℕ (sucf (sucf (sucf (sucf (zerof {1}))))))
  (s≤s (s≤s (s≤s z≤n)))
  (eq_cong toℕ P)

prfNoteq6--2,5 : sucf (sucf (zerof {3})) ≢ sucf (sucf (sucf (sucf (sucf (zerof {0})))))
prfNoteq6--2,5 = λ P → noteq
  (toℕ (sucf (sucf (zerof {3}))))
  (toℕ (sucf (sucf (sucf (sucf (sucf (zerof {0})))))))
  (s≤s (s≤s (s≤s z≤n)))
  (eq_cong toℕ P)

prfNoteq6--3,4 : sucf (sucf (sucf (zerof {2}))) ≢ sucf (sucf (sucf (sucf (zerof {1}))))
prfNoteq6--3,4 = λ P → noteq
  (toℕ (sucf (sucf (sucf (zerof {2})))))
  (toℕ (sucf (sucf (sucf (sucf (zerof {1}))))))
  (s≤s (s≤s (s≤s (s≤s z≤n))))
  (eq_cong toℕ P)

prfNoteq6--3,5 : sucf (sucf (sucf (zerof {2}))) ≢ sucf (sucf (sucf (sucf (sucf (zerof {0})))))
prfNoteq6--3,5 = λ P → noteq
  (toℕ (sucf (sucf (sucf (zerof {2})))))
  (toℕ (sucf (sucf (sucf (sucf (sucf (zerof {0})))))))
  (s≤s (s≤s (s≤s (s≤s z≤n))))
  (eq_cong toℕ P)

prfNoteq6--4,5 : sucf (sucf (sucf (sucf (zerof {1})))) ≢ sucf (sucf (sucf (sucf (sucf (zerof {0})))))
prfNoteq6--4,5 = λ P → noteq
  (toℕ (sucf (sucf (sucf (sucf (zerof {1}))))))
  (toℕ (sucf (sucf (sucf (sucf (sucf (zerof {0})))))))
  (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))
  (eq_cong toℕ P)

----------------
-- Представление о списке и его элементах.
----------------

p_0,1,2,3,4,5 = zerof {5} — ((sucf (zerof {4})) — ((sucf (sucf (zerof {3}))) — ((sucf (sucf (sucf (zerof {2})))) — ((sucf (sucf (sucf (sucf (zerof {1}))))) — ((sucf (sucf (sucf (sucf (sucf (zerof {0})))))) — «»)))))

p_1,0,2,3,4,5 = (sucf (zerof {4})) — (zerof {5} — ((sucf (sucf (zerof {3}))) — ((sucf (sucf (sucf (zerof {2})))) — ((sucf (sucf (sucf (sucf (zerof {1}))))) — ((sucf (sucf (sucf (sucf (sucf (zerof {0})))))) — «»)))))

p_1,0,3,2,4,5 = (sucf (zerof {4})) — (zerof {5} — ((sucf (sucf (sucf (zerof {2})))) — ((sucf (sucf (zerof {3}))) — ((sucf (sucf (sucf (sucf (zerof {1}))))) — ((sucf (sucf (sucf (sucf (sucf (zerof {0})))))) — «»)))))

p_1,2,0,3,4,5 = (sucf (zerof {4})) — ((sucf (sucf (zerof {3}))) — (zerof {5} — ((sucf (sucf (sucf (zerof {2})))) — ((sucf (sucf (sucf (sucf (zerof {1}))))) — ((sucf (sucf (sucf (sucf (sucf (zerof {0})))))) — «»)))))

p_1,2,3,0,4,5 = (sucf (zerof {4})) — ((sucf (sucf (zerof {3}))) — ((sucf (sucf (sucf (zerof {2})))) — (zerof {5} — ((sucf (sucf (sucf (sucf (zerof {1}))))) — ((sucf (sucf (sucf (sucf (sucf (zerof {0})))))) — «»)))))

p_1,3,0,2,4,5 = (sucf (zerof {4})) — ((sucf (sucf (sucf (zerof {2})))) — (zerof {5} — ((sucf (sucf (zerof {3}))) — ((sucf (sucf (sucf (sucf (zerof {1}))))) — ((sucf (sucf (sucf (sucf (sucf (zerof {0})))))) — «»)))))

p_2,0,1,3,4,5 = (sucf (sucf (zerof {3}))) — (zerof {5} — ((sucf (zerof {4})) — ((sucf (sucf (sucf (zerof {2})))) — ((sucf (sucf (sucf (sucf (zerof {1}))))) — ((sucf (sucf (sucf (sucf (sucf (zerof {0})))))) — «»)))))

p_2,0,3,1,4,5 = (sucf (sucf (zerof {3}))) — (zerof {5} — ((sucf (sucf (sucf (zerof {2})))) — ((sucf (zerof {4})) — ((sucf (sucf (sucf (sucf (zerof {1}))))) — ((sucf (sucf (sucf (sucf (sucf (zerof {0})))))) — «»)))))

p_2,3,0,1,4,5 = (sucf (sucf (zerof {3}))) — ((sucf (sucf (sucf (zerof {2})))) — (zerof {5} — ((sucf (zerof {4})) — ((sucf (sucf (sucf (sucf (zerof {1}))))) — ((sucf (sucf (sucf (sucf (sucf (zerof {0})))))) — «»)))))

p_3,0,1,2,4,5 = (sucf (sucf (sucf (zerof {2})))) — (zerof {5} — ((sucf (zerof {4})) — ((sucf (sucf (zerof {3}))) — ((sucf (sucf (sucf (sucf (zerof {1}))))) — ((sucf (sucf (sucf (sucf (sucf (zerof {0})))))) — «»)))))

p_3,0,2,1,4,5 = (sucf (sucf (sucf (zerof {2})))) — (zerof {5} — ((sucf (sucf (zerof {3}))) — ((sucf (zerof {4})) — ((sucf (sucf (sucf (sucf (zerof {1}))))) — ((sucf (sucf (sucf (sucf (sucf (zerof {0})))))) — «»)))))

p_3,1,0,2,4,5 = (sucf (sucf (sucf (zerof {2})))) — ((sucf (zerof {4})) — (zerof {5} — ((sucf (sucf (zerof {3}))) — ((sucf (sucf (sucf (sucf (zerof {1}))))) — ((sucf (sucf (sucf (sucf (sucf (zerof {0})))))) — «»)))))

p_3,1,2,0,4,5 = (sucf (sucf (sucf (zerof {2})))) — ((sucf (zerof {4})) — ((sucf (sucf (zerof {3}))) — (zerof {5} — ((sucf (sucf (sucf (sucf (zerof {1}))))) — ((sucf (sucf (sucf (sucf (sucf (zerof {0})))))) — «»)))))

p_3,2,0,1,4,5 = (sucf (sucf (sucf (zerof {2})))) — ((sucf (sucf (zerof {3}))) — (zerof {5} — ((sucf (zerof {4})) — ((sucf (sucf (sucf (sucf (zerof {1}))))) — ((sucf (sucf (sucf (sucf (sucf (zerof {0})))))) — «»)))))

p_3,2,1,0,4,5 = (sucf (sucf (sucf (zerof {2})))) — ((sucf (sucf (zerof {3}))) — ((sucf (zerof {4})) — (zerof {5} — ((sucf (sucf (sucf (sucf (zerof {1}))))) — ((sucf (sucf (sucf (sucf (sucf (zerof {0})))))) — «»)))))

p_0,1,2,3,5,4 = zerof {5} — ((sucf (zerof {4})) — ((sucf (sucf (zerof {3}))) — ((sucf (sucf (sucf (zerof {2})))) — ((sucf (sucf (sucf (sucf (sucf (zerof {0})))))) — ((sucf (sucf (sucf (sucf (zerof {1}))))) — «»)))))

p_1,0,2,3,5,4 = (sucf (zerof {4})) — (zerof {5} — ((sucf (sucf (zerof {3}))) — ((sucf (sucf (sucf (zerof {2})))) — ((sucf (sucf (sucf (sucf (sucf (zerof {0})))))) — ((sucf (sucf (sucf (sucf (zerof {1}))))) — «»)))))

p_1,0,3,2,5,4 = (sucf (zerof {4})) — (zerof {5} — ((sucf (sucf (sucf (zerof {2})))) — ((sucf (sucf (zerof {3}))) — ((sucf (sucf (sucf (sucf (sucf (zerof {0})))))) — ((sucf (sucf (sucf (sucf (zerof {1}))))) — «»)))))

p_1,2,0,3,5,4 = (sucf (zerof {4})) — ((sucf (sucf (zerof {3}))) — (zerof {5} — ((sucf (sucf (sucf (zerof {2})))) — ((sucf (sucf (sucf (sucf (sucf (zerof {0})))))) — ((sucf (sucf (sucf (sucf (zerof {1}))))) — «»)))))

p_1,2,3,0,5,4 = (sucf (zerof {4})) — ((sucf (sucf (zerof {3}))) — ((sucf (sucf (sucf (zerof {2})))) — (zerof {5} — ((sucf (sucf (sucf (sucf (sucf (zerof {0})))))) — ((sucf (sucf (sucf (sucf (zerof {1}))))) — «»)))))

p_1,3,0,2,5,4 = (sucf (zerof {4})) — ((sucf (sucf (sucf (zerof {2})))) — (zerof {5} — ((sucf (sucf (zerof {3}))) — ((sucf (sucf (sucf (sucf (sucf (zerof {0})))))) — ((sucf (sucf (sucf (sucf (zerof {1}))))) — «»)))))

p_2,0,1,3,5,4 = (sucf (sucf (zerof {3}))) — (zerof {5} — ((sucf (zerof {4})) — ((sucf (sucf (sucf (zerof {2})))) — ((sucf (sucf (sucf (sucf (sucf (zerof {0})))))) — ((sucf (sucf (sucf (sucf (zerof {1}))))) — «»)))))

p_2,0,3,1,5,4 = (sucf (sucf (zerof {3}))) — (zerof {5} — ((sucf (sucf (sucf (zerof {2})))) — ((sucf (zerof {4})) — ((sucf (sucf (sucf (sucf (sucf (zerof {0})))))) — ((sucf (sucf (sucf (sucf (zerof {1}))))) — «»)))))

p_2,3,0,1,5,4 = (sucf (sucf (zerof {3}))) — ((sucf (sucf (sucf (zerof {2})))) — (zerof {5} — ((sucf (zerof {4})) — ((sucf (sucf (sucf (sucf (sucf (zerof {0})))))) — ((sucf (sucf (sucf (sucf (zerof {1}))))) — «»)))))

p_3,0,1,2,5,4 = (sucf (sucf (sucf (zerof {2})))) — (zerof {5} — ((sucf (zerof {4})) — ((sucf (sucf (zerof {3}))) — ((sucf (sucf (sucf (sucf (sucf (zerof {0})))))) — ((sucf (sucf (sucf (sucf (zerof {1}))))) — «»)))))

p_3,0,2,1,5,4 = (sucf (sucf (sucf (zerof {2})))) — (zerof {5} — ((sucf (sucf (zerof {3}))) — ((sucf (zerof {4})) — ((sucf (sucf (sucf (sucf (sucf (zerof {0})))))) — ((sucf (sucf (sucf (sucf (zerof {1}))))) — «»)))))

p_3,1,0,2,5,4 = (sucf (sucf (sucf (zerof {2})))) — ((sucf (zerof {4})) — (zerof {5} — ((sucf (sucf (zerof {3}))) — ((sucf (sucf (sucf (sucf (sucf (zerof {0})))))) — ((sucf (sucf (sucf (sucf (zerof {1}))))) — «»)))))

p_3,1,2,0,5,4 = (sucf (sucf (sucf (zerof {2})))) — ((sucf (zerof {4})) — ((sucf (sucf (zerof {3}))) — (zerof {5} — ((sucf (sucf (sucf (sucf (sucf (zerof {0})))))) — ((sucf (sucf (sucf (sucf (zerof {1}))))) — «»)))))

p_3,2,0,1,5,4 = (sucf (sucf (sucf (zerof {2})))) — ((sucf (sucf (zerof {3}))) — (zerof {5} — ((sucf (zerof {4})) — ((sucf (sucf (sucf (sucf (sucf (zerof {0})))))) — ((sucf (sucf (sucf (sucf (zerof {1}))))) — «»)))))

p_3,2,1,0,5,4 = (sucf (sucf (sucf (zerof {2})))) — ((sucf (sucf (zerof {3}))) — ((sucf (zerof {4})) — (zerof {5} — ((sucf (sucf (sucf (sucf (sucf (zerof {0})))))) — ((sucf (sucf (sucf (sucf (zerof {1}))))) — «»)))))

lis = p_0,1,2,3,4,5 ∷ p_1,0,2,3,4,5 ∷ p_1,0,3,2,4,5 ∷ p_1,2,0,3,4,5 ∷ p_1,2,3,0,4,5 ∷ p_1,3,0,2,4,5 ∷ p_2,0,1,3,4,5 ∷ p_2,0,3,1,4,5 ∷ p_2,3,0,1,4,5 ∷ p_3,0,1,2,4,5 ∷ p_3,0,2,1,4,5 ∷ p_3,1,0,2,4,5 ∷ p_3,1,2,0,4,5 ∷ p_3,2,0,1,4,5 ∷ p_3,2,1,0,4,5 ∷ p_0,1,2,3,5,4 ∷ p_1,0,2,3,5,4 ∷ p_1,0,3,2,5,4 ∷ p_1,2,0,3,5,4 ∷ p_1,2,3,0,5,4 ∷ p_1,3,0,2,5,4 ∷ p_2,0,1,3,5,4 ∷ p_2,0,3,1,5,4 ∷ p_2,3,0,1,5,4 ∷ p_3,0,1,2,5,4 ∷ p_3,0,2,1,5,4 ∷ p_3,1,0,2,5,4 ∷ p_3,1,2,0,5,4 ∷ p_3,2,0,1,5,4 ∷ p_3,2,1,0,5,4 ∷ []

----------------
-- Каждый элемент списка — перестановка.
----------------

u_0,1,2,3,4,5 : (i j : Fin 6) → (i ≢ j) → nth p_0,1,2,3,4,5 i ≢ nth p_0,1,2,3,4,5 j 
u_0,1,2,3,4,5 (zerof) (zerof) p = ⊥-elim (p refl)
u_0,1,2,3,4,5 (sucf (zerof)) (sucf (zerof)) p = ⊥-elim (p refl)
u_0,1,2,3,4,5 (sucf (sucf (zerof))) (sucf (sucf (zerof))) p = ⊥-elim (p refl)
u_0,1,2,3,4,5 (sucf (sucf (sucf (zerof)))) (sucf (sucf (sucf (zerof)))) p = ⊥-elim (p refl)
u_0,1,2,3,4,5 (sucf (sucf (sucf (sucf (zerof))))) (sucf (sucf (sucf (sucf (zerof))))) p = ⊥-elim (p refl)
u_0,1,2,3,4,5 (sucf (sucf (sucf (sucf (sucf (zerof)))))) (sucf (sucf (sucf (sucf (sucf (zerof)))))) p = ⊥-elim (p refl)
u_0,1,2,3,4,5 (sucf (sucf (sucf (sucf (sucf (sucf h)))))) _ = ⊥-elim (nolify h) 
u_0,1,2,3,4,5 _ (sucf (sucf (sucf (sucf (sucf (sucf h)))))) = ⊥-elim (nolify h) 

u_0,1,2,3,4,5 (zerof) (sucf (zerof)) p = prfNoteq6--0,1 
u_0,1,2,3,4,5 (sucf (zerof)) (zerof) p = ncom prfNoteq6--0,1 

u_0,1,2,3,4,5 (zerof) (sucf (sucf (zerof))) p = prfNoteq6--0,2 
u_0,1,2,3,4,5 (sucf (sucf (zerof))) (zerof) p = ncom prfNoteq6--0,2 

u_0,1,2,3,4,5 (zerof) (sucf (sucf (sucf (zerof)))) p = prfNoteq6--0,3 
u_0,1,2,3,4,5 (sucf (sucf (sucf (zerof)))) (zerof) p = ncom prfNoteq6--0,3 

u_0,1,2,3,4,5 (zerof) (sucf (sucf (sucf (sucf (zerof))))) p = prfNoteq6--0,4 
u_0,1,2,3,4,5 (sucf (sucf (sucf (sucf (zerof))))) (zerof) p = ncom prfNoteq6--0,4 

u_0,1,2,3,4,5 (zerof) (sucf (sucf (sucf (sucf (sucf (zerof)))))) p = prfNoteq6--0,5 
u_0,1,2,3,4,5 (sucf (sucf (sucf (sucf (sucf (zerof)))))) (zerof) p = ncom prfNoteq6--0,5 

u_0,1,2,3,4,5 (sucf (zerof)) (sucf (sucf (zerof))) p = prfNoteq6--1,2 
u_0,1,2,3,4,5 (sucf (sucf (zerof))) (sucf (zerof)) p = ncom prfNoteq6--1,2 

u_0,1,2,3,4,5 (sucf (zerof)) (sucf (sucf (sucf (zerof)))) p = prfNoteq6--1,3 
u_0,1,2,3,4,5 (sucf (sucf (sucf (zerof)))) (sucf (zerof)) p = ncom prfNoteq6--1,3 

u_0,1,2,3,4,5 (sucf (zerof)) (sucf (sucf (sucf (sucf (zerof))))) p = prfNoteq6--1,4 
u_0,1,2,3,4,5 (sucf (sucf (sucf (sucf (zerof))))) (sucf (zerof)) p = ncom prfNoteq6--1,4 

u_0,1,2,3,4,5 (sucf (zerof)) (sucf (sucf (sucf (sucf (sucf (zerof)))))) p = prfNoteq6--1,5 
u_0,1,2,3,4,5 (sucf (sucf (sucf (sucf (sucf (zerof)))))) (sucf (zerof)) p = ncom prfNoteq6--1,5 

u_0,1,2,3,4,5 (sucf (sucf (zerof))) (sucf (sucf (sucf (zerof)))) p = prfNoteq6--2,3 
u_0,1,2,3,4,5 (sucf (sucf (sucf (zerof)))) (sucf (sucf (zerof))) p = ncom prfNoteq6--2,3 

u_0,1,2,3,4,5 (sucf (sucf (zerof))) (sucf (sucf (sucf (sucf (zerof))))) p = prfNoteq6--2,4 
u_0,1,2,3,4,5 (sucf (sucf (sucf (sucf (zerof))))) (sucf (sucf (zerof))) p = ncom prfNoteq6--2,4 

u_0,1,2,3,4,5 (sucf (sucf (zerof))) (sucf (sucf (sucf (sucf (sucf (zerof)))))) p = prfNoteq6--2,5 
u_0,1,2,3,4,5 (sucf (sucf (sucf (sucf (sucf (zerof)))))) (sucf (sucf (zerof))) p = ncom prfNoteq6--2,5 

u_0,1,2,3,4,5 (sucf (sucf (sucf (zerof)))) (sucf (sucf (sucf (sucf (zerof))))) p = prfNoteq6--3,4 
u_0,1,2,3,4,5 (sucf (sucf (sucf (sucf (zerof))))) (sucf (sucf (sucf (zerof)))) p = ncom prfNoteq6--3,4 

u_0,1,2,3,4,5 (sucf (sucf (sucf (zerof)))) (sucf (sucf (sucf (sucf (sucf (zerof)))))) p = prfNoteq6--3,5 
u_0,1,2,3,4,5 (sucf (sucf (sucf (sucf (sucf (zerof)))))) (sucf (sucf (sucf (zerof)))) p = ncom prfNoteq6--3,5 

u_0,1,2,3,4,5 (sucf (sucf (sucf (sucf (zerof))))) (sucf (sucf (sucf (sucf (sucf (zerof)))))) p = prfNoteq6--4,5 
u_0,1,2,3,4,5 (sucf (sucf (sucf (sucf (sucf (zerof)))))) (sucf (sucf (sucf (sucf (zerof))))) p = ncom prfNoteq6--4,5 

u_1,0,2,3,4,5 : (i j : Fin 6) → (i ≢ j) → nth p_1,0,2,3,4,5 i ≢ nth p_1,0,2,3,4,5 j 
u_1,0,2,3,4,5 (zerof) (zerof) p = ⊥-elim (p refl)
u_1,0,2,3,4,5 (sucf (zerof)) (sucf (zerof)) p = ⊥-elim (p refl)
u_1,0,2,3,4,5 (sucf (sucf (zerof))) (sucf (sucf (zerof))) p = ⊥-elim (p refl)
u_1,0,2,3,4,5 (sucf (sucf (sucf (zerof)))) (sucf (sucf (sucf (zerof)))) p = ⊥-elim (p refl)
u_1,0,2,3,4,5 (sucf (sucf (sucf (sucf (zerof))))) (sucf (sucf (sucf (sucf (zerof))))) p = ⊥-elim (p refl)
u_1,0,2,3,4,5 (sucf (sucf (sucf (sucf (sucf (zerof)))))) (sucf (sucf (sucf (sucf (sucf (zerof)))))) p = ⊥-elim (p refl)
u_1,0,2,3,4,5 (sucf (sucf (sucf (sucf (sucf (sucf h)))))) _ = ⊥-elim (nolify h) 
u_1,0,2,3,4,5 _ (sucf (sucf (sucf (sucf (sucf (sucf h)))))) = ⊥-elim (nolify h) 

u_1,0,2,3,4,5 (zerof) (sucf (zerof)) p = ncom prfNoteq6--0,1 
u_1,0,2,3,4,5 (sucf (zerof)) (zerof) p = prfNoteq6--0,1 

u_1,0,2,3,4,5 (zerof) (sucf (sucf (zerof))) p = prfNoteq6--1,2 
u_1,0,2,3,4,5 (sucf (sucf (zerof))) (zerof) p = ncom prfNoteq6--1,2 

u_1,0,2,3,4,5 (zerof) (sucf (sucf (sucf (zerof)))) p = prfNoteq6--1,3 
u_1,0,2,3,4,5 (sucf (sucf (sucf (zerof)))) (zerof) p = ncom prfNoteq6--1,3 

u_1,0,2,3,4,5 (zerof) (sucf (sucf (sucf (sucf (zerof))))) p = prfNoteq6--1,4 
u_1,0,2,3,4,5 (sucf (sucf (sucf (sucf (zerof))))) (zerof) p = ncom prfNoteq6--1,4 

u_1,0,2,3,4,5 (zerof) (sucf (sucf (sucf (sucf (sucf (zerof)))))) p = prfNoteq6--1,5 
u_1,0,2,3,4,5 (sucf (sucf (sucf (sucf (sucf (zerof)))))) (zerof) p = ncom prfNoteq6--1,5 

u_1,0,2,3,4,5 (sucf (zerof)) (sucf (sucf (zerof))) p = prfNoteq6--0,2 
u_1,0,2,3,4,5 (sucf (sucf (zerof))) (sucf (zerof)) p = ncom prfNoteq6--0,2 

u_1,0,2,3,4,5 (sucf (zerof)) (sucf (sucf (sucf (zerof)))) p = prfNoteq6--0,3 
u_1,0,2,3,4,5 (sucf (sucf (sucf (zerof)))) (sucf (zerof)) p = ncom prfNoteq6--0,3 

u_1,0,2,3,4,5 (sucf (zerof)) (sucf (sucf (sucf (sucf (zerof))))) p = prfNoteq6--0,4 
u_1,0,2,3,4,5 (sucf (sucf (sucf (sucf (zerof))))) (sucf (zerof)) p = ncom prfNoteq6--0,4 

u_1,0,2,3,4,5 (sucf (zerof)) (sucf (sucf (sucf (sucf (sucf (zerof)))))) p = prfNoteq6--0,5 
u_1,0,2,3,4,5 (sucf (sucf (sucf (sucf (sucf (zerof)))))) (sucf (zerof)) p = ncom prfNoteq6--0,5 

u_1,0,2,3,4,5 (sucf (sucf (zerof))) (sucf (sucf (sucf (zerof)))) p = prfNoteq6--2,3 
u_1,0,2,3,4,5 (sucf (sucf (sucf (zerof)))) (sucf (sucf (zerof))) p = ncom prfNoteq6--2,3 

u_1,0,2,3,4,5 (sucf (sucf (zerof))) (sucf (sucf (sucf (sucf (zerof))))) p = prfNoteq6--2,4 
u_1,0,2,3,4,5 (sucf (sucf (sucf (sucf (zerof))))) (sucf (sucf (zerof))) p = ncom prfNoteq6--2,4 

u_1,0,2,3,4,5 (sucf (sucf (zerof))) (sucf (sucf (sucf (sucf (sucf (zerof)))))) p = prfNoteq6--2,5 
u_1,0,2,3,4,5 (sucf (sucf (sucf (sucf (sucf (zerof)))))) (sucf (sucf (zerof))) p = ncom prfNoteq6--2,5 

u_1,0,2,3,4,5 (sucf (sucf (sucf (zerof)))) (sucf (sucf (sucf (sucf (zerof))))) p = prfNoteq6--3,4 
u_1,0,2,3,4,5 (sucf (sucf (sucf (sucf (zerof))))) (sucf (sucf (sucf (zerof)))) p = ncom prfNoteq6--3,4 

u_1,0,2,3,4,5 (sucf (sucf (sucf (zerof)))) (sucf (sucf (sucf (sucf (sucf (zerof)))))) p = prfNoteq6--3,5 
u_1,0,2,3,4,5 (sucf (sucf (sucf (sucf (sucf (zerof)))))) (sucf (sucf (sucf (zerof)))) p = ncom prfNoteq6--3,5 

u_1,0,2,3,4,5 (sucf (sucf (sucf (sucf (zerof))))) (sucf (sucf (sucf (sucf (sucf (zerof)))))) p = prfNoteq6--4,5 
u_1,0,2,3,4,5 (sucf (sucf (sucf (sucf (sucf (zerof)))))) (sucf (sucf (sucf (sucf (zerof))))) p = ncom prfNoteq6--4,5 

u_1,0,3,2,4,5 : (i j : Fin 6) → (i ≢ j) → nth p_1,0,3,2,4,5 i ≢ nth p_1,0,3,2,4,5 j 
u_1,0,3,2,4,5 (zerof) (zerof) p = ⊥-elim (p refl)
u_1,0,3,2,4,5 (sucf (zerof)) (sucf (zerof)) p = ⊥-elim (p refl)
u_1,0,3,2,4,5 (sucf (sucf (zerof))) (sucf (sucf (zerof))) p = ⊥-elim (p refl)
u_1,0,3,2,4,5 (sucf (sucf (sucf (zerof)))) (sucf (sucf (sucf (zerof)))) p = ⊥-elim (p refl)
u_1,0,3,2,4,5 (sucf (sucf (sucf (sucf (zerof))))) (sucf (sucf (sucf (sucf (zerof))))) p = ⊥-elim (p refl)
u_1,0,3,2,4,5 (sucf (sucf (sucf (sucf (sucf (zerof)))))) (sucf (sucf (sucf (sucf (sucf (zerof)))))) p = ⊥-elim (p refl)
u_1,0,3,2,4,5 (sucf (sucf (sucf (sucf (sucf (sucf h)))))) _ = ⊥-elim (nolify h) 
u_1,0,3,2,4,5 _ (sucf (sucf (sucf (sucf (sucf (sucf h)))))) = ⊥-elim (nolify h) 

u_1,0,3,2,4,5 (zerof) (sucf (zerof)) p = ncom prfNoteq6--0,1 
u_1,0,3,2,4,5 (sucf (zerof)) (zerof) p = prfNoteq6--0,1 

u_1,0,3,2,4,5 (zerof) (sucf (sucf (zerof))) p = prfNoteq6--1,3 
u_1,0,3,2,4,5 (sucf (sucf (zerof))) (zerof) p = ncom prfNoteq6--1,3 

u_1,0,3,2,4,5 (zerof) (sucf (sucf (sucf (zerof)))) p = prfNoteq6--1,2 
u_1,0,3,2,4,5 (sucf (sucf (sucf (zerof)))) (zerof) p = ncom prfNoteq6--1,2 

u_1,0,3,2,4,5 (zerof) (sucf (sucf (sucf (sucf (zerof))))) p = prfNoteq6--1,4 
u_1,0,3,2,4,5 (sucf (sucf (sucf (sucf (zerof))))) (zerof) p = ncom prfNoteq6--1,4 

u_1,0,3,2,4,5 (zerof) (sucf (sucf (sucf (sucf (sucf (zerof)))))) p = prfNoteq6--1,5 
u_1,0,3,2,4,5 (sucf (sucf (sucf (sucf (sucf (zerof)))))) (zerof) p = ncom prfNoteq6--1,5 

u_1,0,3,2,4,5 (sucf (zerof)) (sucf (sucf (zerof))) p = prfNoteq6--0,3 
u_1,0,3,2,4,5 (sucf (sucf (zerof))) (sucf (zerof)) p = ncom prfNoteq6--0,3 

u_1,0,3,2,4,5 (sucf (zerof)) (sucf (sucf (sucf (zerof)))) p = prfNoteq6--0,2 
u_1,0,3,2,4,5 (sucf (sucf (sucf (zerof)))) (sucf (zerof)) p = ncom prfNoteq6--0,2 

u_1,0,3,2,4,5 (sucf (zerof)) (sucf (sucf (sucf (sucf (zerof))))) p = prfNoteq6--0,4 
u_1,0,3,2,4,5 (sucf (sucf (sucf (sucf (zerof))))) (sucf (zerof)) p = ncom prfNoteq6--0,4 

u_1,0,3,2,4,5 (sucf (zerof)) (sucf (sucf (sucf (sucf (sucf (zerof)))))) p = prfNoteq6--0,5 
u_1,0,3,2,4,5 (sucf (sucf (sucf (sucf (sucf (zerof)))))) (sucf (zerof)) p = ncom prfNoteq6--0,5 

u_1,0,3,2,4,5 (sucf (sucf (zerof))) (sucf (sucf (sucf (zerof)))) p = ncom prfNoteq6--2,3 
u_1,0,3,2,4,5 (sucf (sucf (sucf (zerof)))) (sucf (sucf (zerof))) p = prfNoteq6--2,3 

u_1,0,3,2,4,5 (sucf (sucf (zerof))) (sucf (sucf (sucf (sucf (zerof))))) p = prfNoteq6--3,4 
u_1,0,3,2,4,5 (sucf (sucf (sucf (sucf (zerof))))) (sucf (sucf (zerof))) p = ncom prfNoteq6--3,4 

u_1,0,3,2,4,5 (sucf (sucf (zerof))) (sucf (sucf (sucf (sucf (sucf (zerof)))))) p = prfNoteq6--3,5 
u_1,0,3,2,4,5 (sucf (sucf (sucf (sucf (sucf (zerof)))))) (sucf (sucf (zerof))) p = ncom prfNoteq6--3,5 

u_1,0,3,2,4,5 (sucf (sucf (sucf (zerof)))) (sucf (sucf (sucf (sucf (zerof))))) p = prfNoteq6--2,4 
u_1,0,3,2,4,5 (sucf (sucf (sucf (sucf (zerof))))) (sucf (sucf (sucf (zerof)))) p = ncom prfNoteq6--2,4 

u_1,0,3,2,4,5 (sucf (sucf (sucf (zerof)))) (sucf (sucf (sucf (sucf (sucf (zerof)))))) p = prfNoteq6--2,5 
u_1,0,3,2,4,5 (sucf (sucf (sucf (sucf (sucf (zerof)))))) (sucf (sucf (sucf (zerof)))) p = ncom prfNoteq6--2,5 

u_1,0,3,2,4,5 (sucf (sucf (sucf (sucf (zerof))))) (sucf (sucf (sucf (sucf (sucf (zerof)))))) p = prfNoteq6--4,5 
u_1,0,3,2,4,5 (sucf (sucf (sucf (sucf (sucf (zerof)))))) (sucf (sucf (sucf (sucf (zerof))))) p = ncom prfNoteq6--4,5 

u_1,2,0,3,4,5 : (i j : Fin 6) → (i ≢ j) → nth p_1,2,0,3,4,5 i ≢ nth p_1,2,0,3,4,5 j 
u_1,2,0,3,4,5 (zerof) (zerof) p = ⊥-elim (p refl)
u_1,2,0,3,4,5 (sucf (zerof)) (sucf (zerof)) p = ⊥-elim (p refl)
u_1,2,0,3,4,5 (sucf (sucf (zerof))) (sucf (sucf (zerof))) p = ⊥-elim (p refl)
u_1,2,0,3,4,5 (sucf (sucf (sucf (zerof)))) (sucf (sucf (sucf (zerof)))) p = ⊥-elim (p refl)
u_1,2,0,3,4,5 (sucf (sucf (sucf (sucf (zerof))))) (sucf (sucf (sucf (sucf (zerof))))) p = ⊥-elim (p refl)
u_1,2,0,3,4,5 (sucf (sucf (sucf (sucf (sucf (zerof)))))) (sucf (sucf (sucf (sucf (sucf (zerof)))))) p = ⊥-elim (p refl)
u_1,2,0,3,4,5 (sucf (sucf (sucf (sucf (sucf (sucf h)))))) _ = ⊥-elim (nolify h) 
u_1,2,0,3,4,5 _ (sucf (sucf (sucf (sucf (sucf (sucf h)))))) = ⊥-elim (nolify h) 

u_1,2,0,3,4,5 (zerof) (sucf (zerof)) p = prfNoteq6--1,2 
u_1,2,0,3,4,5 (sucf (zerof)) (zerof) p = ncom prfNoteq6--1,2 

u_1,2,0,3,4,5 (zerof) (sucf (sucf (zerof))) p = ncom prfNoteq6--0,1 
u_1,2,0,3,4,5 (sucf (sucf (zerof))) (zerof) p = prfNoteq6--0,1 

u_1,2,0,3,4,5 (zerof) (sucf (sucf (sucf (zerof)))) p = prfNoteq6--1,3 
u_1,2,0,3,4,5 (sucf (sucf (sucf (zerof)))) (zerof) p = ncom prfNoteq6--1,3 

u_1,2,0,3,4,5 (zerof) (sucf (sucf (sucf (sucf (zerof))))) p = prfNoteq6--1,4 
u_1,2,0,3,4,5 (sucf (sucf (sucf (sucf (zerof))))) (zerof) p = ncom prfNoteq6--1,4 

u_1,2,0,3,4,5 (zerof) (sucf (sucf (sucf (sucf (sucf (zerof)))))) p = prfNoteq6--1,5 
u_1,2,0,3,4,5 (sucf (sucf (sucf (sucf (sucf (zerof)))))) (zerof) p = ncom prfNoteq6--1,5 

u_1,2,0,3,4,5 (sucf (zerof)) (sucf (sucf (zerof))) p = ncom prfNoteq6--0,2 
u_1,2,0,3,4,5 (sucf (sucf (zerof))) (sucf (zerof)) p = prfNoteq6--0,2 

u_1,2,0,3,4,5 (sucf (zerof)) (sucf (sucf (sucf (zerof)))) p = prfNoteq6--2,3 
u_1,2,0,3,4,5 (sucf (sucf (sucf (zerof)))) (sucf (zerof)) p = ncom prfNoteq6--2,3 

u_1,2,0,3,4,5 (sucf (zerof)) (sucf (sucf (sucf (sucf (zerof))))) p = prfNoteq6--2,4 
u_1,2,0,3,4,5 (sucf (sucf (sucf (sucf (zerof))))) (sucf (zerof)) p = ncom prfNoteq6--2,4 

u_1,2,0,3,4,5 (sucf (zerof)) (sucf (sucf (sucf (sucf (sucf (zerof)))))) p = prfNoteq6--2,5 
u_1,2,0,3,4,5 (sucf (sucf (sucf (sucf (sucf (zerof)))))) (sucf (zerof)) p = ncom prfNoteq6--2,5 

u_1,2,0,3,4,5 (sucf (sucf (zerof))) (sucf (sucf (sucf (zerof)))) p = prfNoteq6--0,3 
u_1,2,0,3,4,5 (sucf (sucf (sucf (zerof)))) (sucf (sucf (zerof))) p = ncom prfNoteq6--0,3 

u_1,2,0,3,4,5 (sucf (sucf (zerof))) (sucf (sucf (sucf (sucf (zerof))))) p = prfNoteq6--0,4 
u_1,2,0,3,4,5 (sucf (sucf (sucf (sucf (zerof))))) (sucf (sucf (zerof))) p = ncom prfNoteq6--0,4 

u_1,2,0,3,4,5 (sucf (sucf (zerof))) (sucf (sucf (sucf (sucf (sucf (zerof)))))) p = prfNoteq6--0,5 
u_1,2,0,3,4,5 (sucf (sucf (sucf (sucf (sucf (zerof)))))) (sucf (sucf (zerof))) p = ncom prfNoteq6--0,5 

u_1,2,0,3,4,5 (sucf (sucf (sucf (zerof)))) (sucf (sucf (sucf (sucf (zerof))))) p = prfNoteq6--3,4 
u_1,2,0,3,4,5 (sucf (sucf (sucf (sucf (zerof))))) (sucf (sucf (sucf (zerof)))) p = ncom prfNoteq6--3,4 

u_1,2,0,3,4,5 (sucf (sucf (sucf (zerof)))) (sucf (sucf (sucf (sucf (sucf (zerof)))))) p = prfNoteq6--3,5 
u_1,2,0,3,4,5 (sucf (sucf (sucf (sucf (sucf (zerof)))))) (sucf (sucf (sucf (zerof)))) p = ncom prfNoteq6--3,5 

u_1,2,0,3,4,5 (sucf (sucf (sucf (sucf (zerof))))) (sucf (sucf (sucf (sucf (sucf (zerof)))))) p = prfNoteq6--4,5 
u_1,2,0,3,4,5 (sucf (sucf (sucf (sucf (sucf (zerof)))))) (sucf (sucf (sucf (sucf (zerof))))) p = ncom prfNoteq6--4,5 

u_1,2,3,0,4,5 : (i j : Fin 6) → (i ≢ j) → nth p_1,2,3,0,4,5 i ≢ nth p_1,2,3,0,4,5 j 
u_1,2,3,0,4,5 (zerof) (zerof) p = ⊥-elim (p refl)
u_1,2,3,0,4,5 (sucf (zerof)) (sucf (zerof)) p = ⊥-elim (p refl)
u_1,2,3,0,4,5 (sucf (sucf (zerof))) (sucf (sucf (zerof))) p = ⊥-elim (p refl)
u_1,2,3,0,4,5 (sucf (sucf (sucf (zerof)))) (sucf (sucf (sucf (zerof)))) p = ⊥-elim (p refl)
u_1,2,3,0,4,5 (sucf (sucf (sucf (sucf (zerof))))) (sucf (sucf (sucf (sucf (zerof))))) p = ⊥-elim (p refl)
u_1,2,3,0,4,5 (sucf (sucf (sucf (sucf (sucf (zerof)))))) (sucf (sucf (sucf (sucf (sucf (zerof)))))) p = ⊥-elim (p refl)
u_1,2,3,0,4,5 (sucf (sucf (sucf (sucf (sucf (sucf h)))))) _ = ⊥-elim (nolify h) 
u_1,2,3,0,4,5 _ (sucf (sucf (sucf (sucf (sucf (sucf h)))))) = ⊥-elim (nolify h) 

u_1,2,3,0,4,5 (zerof) (sucf (zerof)) p = prfNoteq6--1,2 
u_1,2,3,0,4,5 (sucf (zerof)) (zerof) p = ncom prfNoteq6--1,2 

u_1,2,3,0,4,5 (zerof) (sucf (sucf (zerof))) p = prfNoteq6--1,3 
u_1,2,3,0,4,5 (sucf (sucf (zerof))) (zerof) p = ncom prfNoteq6--1,3 

u_1,2,3,0,4,5 (zerof) (sucf (sucf (sucf (zerof)))) p = ncom prfNoteq6--0,1 
u_1,2,3,0,4,5 (sucf (sucf (sucf (zerof)))) (zerof) p = prfNoteq6--0,1 

u_1,2,3,0,4,5 (zerof) (sucf (sucf (sucf (sucf (zerof))))) p = prfNoteq6--1,4 
u_1,2,3,0,4,5 (sucf (sucf (sucf (sucf (zerof))))) (zerof) p = ncom prfNoteq6--1,4 

u_1,2,3,0,4,5 (zerof) (sucf (sucf (sucf (sucf (sucf (zerof)))))) p = prfNoteq6--1,5 
u_1,2,3,0,4,5 (sucf (sucf (sucf (sucf (sucf (zerof)))))) (zerof) p = ncom prfNoteq6--1,5 

u_1,2,3,0,4,5 (sucf (zerof)) (sucf (sucf (zerof))) p = prfNoteq6--2,3 
u_1,2,3,0,4,5 (sucf (sucf (zerof))) (sucf (zerof)) p = ncom prfNoteq6--2,3 

u_1,2,3,0,4,5 (sucf (zerof)) (sucf (sucf (sucf (zerof)))) p = ncom prfNoteq6--0,2 
u_1,2,3,0,4,5 (sucf (sucf (sucf (zerof)))) (sucf (zerof)) p = prfNoteq6--0,2 

u_1,2,3,0,4,5 (sucf (zerof)) (sucf (sucf (sucf (sucf (zerof))))) p = prfNoteq6--2,4 
u_1,2,3,0,4,5 (sucf (sucf (sucf (sucf (zerof))))) (sucf (zerof)) p = ncom prfNoteq6--2,4 

u_1,2,3,0,4,5 (sucf (zerof)) (sucf (sucf (sucf (sucf (sucf (zerof)))))) p = prfNoteq6--2,5 
u_1,2,3,0,4,5 (sucf (sucf (sucf (sucf (sucf (zerof)))))) (sucf (zerof)) p = ncom prfNoteq6--2,5 

u_1,2,3,0,4,5 (sucf (sucf (zerof))) (sucf (sucf (sucf (zerof)))) p = ncom prfNoteq6--0,3 
u_1,2,3,0,4,5 (sucf (sucf (sucf (zerof)))) (sucf (sucf (zerof))) p = prfNoteq6--0,3 

u_1,2,3,0,4,5 (sucf (sucf (zerof))) (sucf (sucf (sucf (sucf (zerof))))) p = prfNoteq6--3,4 
u_1,2,3,0,4,5 (sucf (sucf (sucf (sucf (zerof))))) (sucf (sucf (zerof))) p = ncom prfNoteq6--3,4 

u_1,2,3,0,4,5 (sucf (sucf (zerof))) (sucf (sucf (sucf (sucf (sucf (zerof)))))) p = prfNoteq6--3,5 
u_1,2,3,0,4,5 (sucf (sucf (sucf (sucf (sucf (zerof)))))) (sucf (sucf (zerof))) p = ncom prfNoteq6--3,5 

u_1,2,3,0,4,5 (sucf (sucf (sucf (zerof)))) (sucf (sucf (sucf (sucf (zerof))))) p = prfNoteq6--0,4 
u_1,2,3,0,4,5 (sucf (sucf (sucf (sucf (zerof))))) (sucf (sucf (sucf (zerof)))) p = ncom prfNoteq6--0,4 

u_1,2,3,0,4,5 (sucf (sucf (sucf (zerof)))) (sucf (sucf (sucf (sucf (sucf (zerof)))))) p = prfNoteq6--0,5 
u_1,2,3,0,4,5 (sucf (sucf (sucf (sucf (sucf (zerof)))))) (sucf (sucf (sucf (zerof)))) p = ncom prfNoteq6--0,5 

u_1,2,3,0,4,5 (sucf (sucf (sucf (sucf (zerof))))) (sucf (sucf (sucf (sucf (sucf (zerof)))))) p = prfNoteq6--4,5 
u_1,2,3,0,4,5 (sucf (sucf (sucf (sucf (sucf (zerof)))))) (sucf (sucf (sucf (sucf (zerof))))) p = ncom prfNoteq6--4,5 

u_1,3,0,2,4,5 : (i j : Fin 6) → (i ≢ j) → nth p_1,3,0,2,4,5 i ≢ nth p_1,3,0,2,4,5 j 
u_1,3,0,2,4,5 (zerof) (zerof) p = ⊥-elim (p refl)
u_1,3,0,2,4,5 (sucf (zerof)) (sucf (zerof)) p = ⊥-elim (p refl)
u_1,3,0,2,4,5 (sucf (sucf (zerof))) (sucf (sucf (zerof))) p = ⊥-elim (p refl)
u_1,3,0,2,4,5 (sucf (sucf (sucf (zerof)))) (sucf (sucf (sucf (zerof)))) p = ⊥-elim (p refl)
u_1,3,0,2,4,5 (sucf (sucf (sucf (sucf (zerof))))) (sucf (sucf (sucf (sucf (zerof))))) p = ⊥-elim (p refl)
u_1,3,0,2,4,5 (sucf (sucf (sucf (sucf (sucf (zerof)))))) (sucf (sucf (sucf (sucf (sucf (zerof)))))) p = ⊥-elim (p refl)
u_1,3,0,2,4,5 (sucf (sucf (sucf (sucf (sucf (sucf h)))))) _ = ⊥-elim (nolify h) 
u_1,3,0,2,4,5 _ (sucf (sucf (sucf (sucf (sucf (sucf h)))))) = ⊥-elim (nolify h) 

u_1,3,0,2,4,5 (zerof) (sucf (zerof)) p = prfNoteq6--1,3 
u_1,3,0,2,4,5 (sucf (zerof)) (zerof) p = ncom prfNoteq6--1,3 

u_1,3,0,2,4,5 (zerof) (sucf (sucf (zerof))) p = ncom prfNoteq6--0,1 
u_1,3,0,2,4,5 (sucf (sucf (zerof))) (zerof) p = prfNoteq6--0,1 

u_1,3,0,2,4,5 (zerof) (sucf (sucf (sucf (zerof)))) p = prfNoteq6--1,2 
u_1,3,0,2,4,5 (sucf (sucf (sucf (zerof)))) (zerof) p = ncom prfNoteq6--1,2 

u_1,3,0,2,4,5 (zerof) (sucf (sucf (sucf (sucf (zerof))))) p = prfNoteq6--1,4 
u_1,3,0,2,4,5 (sucf (sucf (sucf (sucf (zerof))))) (zerof) p = ncom prfNoteq6--1,4 

u_1,3,0,2,4,5 (zerof) (sucf (sucf (sucf (sucf (sucf (zerof)))))) p = prfNoteq6--1,5 
u_1,3,0,2,4,5 (sucf (sucf (sucf (sucf (sucf (zerof)))))) (zerof) p = ncom prfNoteq6--1,5 

u_1,3,0,2,4,5 (sucf (zerof)) (sucf (sucf (zerof))) p = ncom prfNoteq6--0,3 
u_1,3,0,2,4,5 (sucf (sucf (zerof))) (sucf (zerof)) p = prfNoteq6--0,3 

u_1,3,0,2,4,5 (sucf (zerof)) (sucf (sucf (sucf (zerof)))) p = ncom prfNoteq6--2,3 
u_1,3,0,2,4,5 (sucf (sucf (sucf (zerof)))) (sucf (zerof)) p = prfNoteq6--2,3 

u_1,3,0,2,4,5 (sucf (zerof)) (sucf (sucf (sucf (sucf (zerof))))) p = prfNoteq6--3,4 
u_1,3,0,2,4,5 (sucf (sucf (sucf (sucf (zerof))))) (sucf (zerof)) p = ncom prfNoteq6--3,4 

u_1,3,0,2,4,5 (sucf (zerof)) (sucf (sucf (sucf (sucf (sucf (zerof)))))) p = prfNoteq6--3,5 
u_1,3,0,2,4,5 (sucf (sucf (sucf (sucf (sucf (zerof)))))) (sucf (zerof)) p = ncom prfNoteq6--3,5 

u_1,3,0,2,4,5 (sucf (sucf (zerof))) (sucf (sucf (sucf (zerof)))) p = prfNoteq6--0,2 
u_1,3,0,2,4,5 (sucf (sucf (sucf (zerof)))) (sucf (sucf (zerof))) p = ncom prfNoteq6--0,2 

u_1,3,0,2,4,5 (sucf (sucf (zerof))) (sucf (sucf (sucf (sucf (zerof))))) p = prfNoteq6--0,4 
u_1,3,0,2,4,5 (sucf (sucf (sucf (sucf (zerof))))) (sucf (sucf (zerof))) p = ncom prfNoteq6--0,4 

u_1,3,0,2,4,5 (sucf (sucf (zerof))) (sucf (sucf (sucf (sucf (sucf (zerof)))))) p = prfNoteq6--0,5 
u_1,3,0,2,4,5 (sucf (sucf (sucf (sucf (sucf (zerof)))))) (sucf (sucf (zerof))) p = ncom prfNoteq6--0,5 

u_1,3,0,2,4,5 (sucf (sucf (sucf (zerof)))) (sucf (sucf (sucf (sucf (zerof))))) p = prfNoteq6--2,4 
u_1,3,0,2,4,5 (sucf (sucf (sucf (sucf (zerof))))) (sucf (sucf (sucf (zerof)))) p = ncom prfNoteq6--2,4 

u_1,3,0,2,4,5 (sucf (sucf (sucf (zerof)))) (sucf (sucf (sucf (sucf (sucf (zerof)))))) p = prfNoteq6--2,5 
u_1,3,0,2,4,5 (sucf (sucf (sucf (sucf (sucf (zerof)))))) (sucf (sucf (sucf (zerof)))) p = ncom prfNoteq6--2,5 

u_1,3,0,2,4,5 (sucf (sucf (sucf (sucf (zerof))))) (sucf (sucf (sucf (sucf (sucf (zerof)))))) p = prfNoteq6--4,5 
u_1,3,0,2,4,5 (sucf (sucf (sucf (sucf (sucf (zerof)))))) (sucf (sucf (sucf (sucf (zerof))))) p = ncom prfNoteq6--4,5 

u_2,0,1,3,4,5 : (i j : Fin 6) → (i ≢ j) → nth p_2,0,1,3,4,5 i ≢ nth p_2,0,1,3,4,5 j 
u_2,0,1,3,4,5 (zerof) (zerof) p = ⊥-elim (p refl)
u_2,0,1,3,4,5 (sucf (zerof)) (sucf (zerof)) p = ⊥-elim (p refl)
u_2,0,1,3,4,5 (sucf (sucf (zerof))) (sucf (sucf (zerof))) p = ⊥-elim (p refl)
u_2,0,1,3,4,5 (sucf (sucf (sucf (zerof)))) (sucf (sucf (sucf (zerof)))) p = ⊥-elim (p refl)
u_2,0,1,3,4,5 (sucf (sucf (sucf (sucf (zerof))))) (sucf (sucf (sucf (sucf (zerof))))) p = ⊥-elim (p refl)
u_2,0,1,3,4,5 (sucf (sucf (sucf (sucf (sucf (zerof)))))) (sucf (sucf (sucf (sucf (sucf (zerof)))))) p = ⊥-elim (p refl)
u_2,0,1,3,4,5 (sucf (sucf (sucf (sucf (sucf (sucf h)))))) _ = ⊥-elim (nolify h) 
u_2,0,1,3,4,5 _ (sucf (sucf (sucf (sucf (sucf (sucf h)))))) = ⊥-elim (nolify h) 

u_2,0,1,3,4,5 (zerof) (sucf (zerof)) p = ncom prfNoteq6--0,2 
u_2,0,1,3,4,5 (sucf (zerof)) (zerof) p = prfNoteq6--0,2 

u_2,0,1,3,4,5 (zerof) (sucf (sucf (zerof))) p = ncom prfNoteq6--1,2 
u_2,0,1,3,4,5 (sucf (sucf (zerof))) (zerof) p = prfNoteq6--1,2 

u_2,0,1,3,4,5 (zerof) (sucf (sucf (sucf (zerof)))) p = prfNoteq6--2,3 
u_2,0,1,3,4,5 (sucf (sucf (sucf (zerof)))) (zerof) p = ncom prfNoteq6--2,3 

u_2,0,1,3,4,5 (zerof) (sucf (sucf (sucf (sucf (zerof))))) p = prfNoteq6--2,4 
u_2,0,1,3,4,5 (sucf (sucf (sucf (sucf (zerof))))) (zerof) p = ncom prfNoteq6--2,4 

u_2,0,1,3,4,5 (zerof) (sucf (sucf (sucf (sucf (sucf (zerof)))))) p = prfNoteq6--2,5 
u_2,0,1,3,4,5 (sucf (sucf (sucf (sucf (sucf (zerof)))))) (zerof) p = ncom prfNoteq6--2,5 

u_2,0,1,3,4,5 (sucf (zerof)) (sucf (sucf (zerof))) p = prfNoteq6--0,1 
u_2,0,1,3,4,5 (sucf (sucf (zerof))) (sucf (zerof)) p = ncom prfNoteq6--0,1 

u_2,0,1,3,4,5 (sucf (zerof)) (sucf (sucf (sucf (zerof)))) p = prfNoteq6--0,3 
u_2,0,1,3,4,5 (sucf (sucf (sucf (zerof)))) (sucf (zerof)) p = ncom prfNoteq6--0,3 

u_2,0,1,3,4,5 (sucf (zerof)) (sucf (sucf (sucf (sucf (zerof))))) p = prfNoteq6--0,4 
u_2,0,1,3,4,5 (sucf (sucf (sucf (sucf (zerof))))) (sucf (zerof)) p = ncom prfNoteq6--0,4 

u_2,0,1,3,4,5 (sucf (zerof)) (sucf (sucf (sucf (sucf (sucf (zerof)))))) p = prfNoteq6--0,5 
u_2,0,1,3,4,5 (sucf (sucf (sucf (sucf (sucf (zerof)))))) (sucf (zerof)) p = ncom prfNoteq6--0,5 

u_2,0,1,3,4,5 (sucf (sucf (zerof))) (sucf (sucf (sucf (zerof)))) p = prfNoteq6--1,3 
u_2,0,1,3,4,5 (sucf (sucf (sucf (zerof)))) (sucf (sucf (zerof))) p = ncom prfNoteq6--1,3 

u_2,0,1,3,4,5 (sucf (sucf (zerof))) (sucf (sucf (sucf (sucf (zerof))))) p = prfNoteq6--1,4 
u_2,0,1,3,4,5 (sucf (sucf (sucf (sucf (zerof))))) (sucf (sucf (zerof))) p = ncom prfNoteq6--1,4 

u_2,0,1,3,4,5 (sucf (sucf (zerof))) (sucf (sucf (sucf (sucf (sucf (zerof)))))) p = prfNoteq6--1,5 
u_2,0,1,3,4,5 (sucf (sucf (sucf (sucf (sucf (zerof)))))) (sucf (sucf (zerof))) p = ncom prfNoteq6--1,5 

u_2,0,1,3,4,5 (sucf (sucf (sucf (zerof)))) (sucf (sucf (sucf (sucf (zerof))))) p = prfNoteq6--3,4 
u_2,0,1,3,4,5 (sucf (sucf (sucf (sucf (zerof))))) (sucf (sucf (sucf (zerof)))) p = ncom prfNoteq6--3,4 

u_2,0,1,3,4,5 (sucf (sucf (sucf (zerof)))) (sucf (sucf (sucf (sucf (sucf (zerof)))))) p = prfNoteq6--3,5 
u_2,0,1,3,4,5 (sucf (sucf (sucf (sucf (sucf (zerof)))))) (sucf (sucf (sucf (zerof)))) p = ncom prfNoteq6--3,5 

u_2,0,1,3,4,5 (sucf (sucf (sucf (sucf (zerof))))) (sucf (sucf (sucf (sucf (sucf (zerof)))))) p = prfNoteq6--4,5 
u_2,0,1,3,4,5 (sucf (sucf (sucf (sucf (sucf (zerof)))))) (sucf (sucf (sucf (sucf (zerof))))) p = ncom prfNoteq6--4,5 

u_2,0,3,1,4,5 : (i j : Fin 6) → (i ≢ j) → nth p_2,0,3,1,4,5 i ≢ nth p_2,0,3,1,4,5 j 
u_2,0,3,1,4,5 (zerof) (zerof) p = ⊥-elim (p refl)
u_2,0,3,1,4,5 (sucf (zerof)) (sucf (zerof)) p = ⊥-elim (p refl)
u_2,0,3,1,4,5 (sucf (sucf (zerof))) (sucf (sucf (zerof))) p = ⊥-elim (p refl)
u_2,0,3,1,4,5 (sucf (sucf (sucf (zerof)))) (sucf (sucf (sucf (zerof)))) p = ⊥-elim (p refl)
u_2,0,3,1,4,5 (sucf (sucf (sucf (sucf (zerof))))) (sucf (sucf (sucf (sucf (zerof))))) p = ⊥-elim (p refl)
u_2,0,3,1,4,5 (sucf (sucf (sucf (sucf (sucf (zerof)))))) (sucf (sucf (sucf (sucf (sucf (zerof)))))) p = ⊥-elim (p refl)
u_2,0,3,1,4,5 (sucf (sucf (sucf (sucf (sucf (sucf h)))))) _ = ⊥-elim (nolify h) 
u_2,0,3,1,4,5 _ (sucf (sucf (sucf (sucf (sucf (sucf h)))))) = ⊥-elim (nolify h) 

u_2,0,3,1,4,5 (zerof) (sucf (zerof)) p = ncom prfNoteq6--0,2 
u_2,0,3,1,4,5 (sucf (zerof)) (zerof) p = prfNoteq6--0,2 

u_2,0,3,1,4,5 (zerof) (sucf (sucf (zerof))) p = prfNoteq6--2,3 
u_2,0,3,1,4,5 (sucf (sucf (zerof))) (zerof) p = ncom prfNoteq6--2,3 

u_2,0,3,1,4,5 (zerof) (sucf (sucf (sucf (zerof)))) p = ncom prfNoteq6--1,2 
u_2,0,3,1,4,5 (sucf (sucf (sucf (zerof)))) (zerof) p = prfNoteq6--1,2 

u_2,0,3,1,4,5 (zerof) (sucf (sucf (sucf (sucf (zerof))))) p = prfNoteq6--2,4 
u_2,0,3,1,4,5 (sucf (sucf (sucf (sucf (zerof))))) (zerof) p = ncom prfNoteq6--2,4 

u_2,0,3,1,4,5 (zerof) (sucf (sucf (sucf (sucf (sucf (zerof)))))) p = prfNoteq6--2,5 
u_2,0,3,1,4,5 (sucf (sucf (sucf (sucf (sucf (zerof)))))) (zerof) p = ncom prfNoteq6--2,5 

u_2,0,3,1,4,5 (sucf (zerof)) (sucf (sucf (zerof))) p = prfNoteq6--0,3 
u_2,0,3,1,4,5 (sucf (sucf (zerof))) (sucf (zerof)) p = ncom prfNoteq6--0,3 

u_2,0,3,1,4,5 (sucf (zerof)) (sucf (sucf (sucf (zerof)))) p = prfNoteq6--0,1 
u_2,0,3,1,4,5 (sucf (sucf (sucf (zerof)))) (sucf (zerof)) p = ncom prfNoteq6--0,1 

u_2,0,3,1,4,5 (sucf (zerof)) (sucf (sucf (sucf (sucf (zerof))))) p = prfNoteq6--0,4 
u_2,0,3,1,4,5 (sucf (sucf (sucf (sucf (zerof))))) (sucf (zerof)) p = ncom prfNoteq6--0,4 

u_2,0,3,1,4,5 (sucf (zerof)) (sucf (sucf (sucf (sucf (sucf (zerof)))))) p = prfNoteq6--0,5 
u_2,0,3,1,4,5 (sucf (sucf (sucf (sucf (sucf (zerof)))))) (sucf (zerof)) p = ncom prfNoteq6--0,5 

u_2,0,3,1,4,5 (sucf (sucf (zerof))) (sucf (sucf (sucf (zerof)))) p = ncom prfNoteq6--1,3 
u_2,0,3,1,4,5 (sucf (sucf (sucf (zerof)))) (sucf (sucf (zerof))) p = prfNoteq6--1,3 

u_2,0,3,1,4,5 (sucf (sucf (zerof))) (sucf (sucf (sucf (sucf (zerof))))) p = prfNoteq6--3,4 
u_2,0,3,1,4,5 (sucf (sucf (sucf (sucf (zerof))))) (sucf (sucf (zerof))) p = ncom prfNoteq6--3,4 

u_2,0,3,1,4,5 (sucf (sucf (zerof))) (sucf (sucf (sucf (sucf (sucf (zerof)))))) p = prfNoteq6--3,5 
u_2,0,3,1,4,5 (sucf (sucf (sucf (sucf (sucf (zerof)))))) (sucf (sucf (zerof))) p = ncom prfNoteq6--3,5 

u_2,0,3,1,4,5 (sucf (sucf (sucf (zerof)))) (sucf (sucf (sucf (sucf (zerof))))) p = prfNoteq6--1,4 
u_2,0,3,1,4,5 (sucf (sucf (sucf (sucf (zerof))))) (sucf (sucf (sucf (zerof)))) p = ncom prfNoteq6--1,4 

u_2,0,3,1,4,5 (sucf (sucf (sucf (zerof)))) (sucf (sucf (sucf (sucf (sucf (zerof)))))) p = prfNoteq6--1,5 
u_2,0,3,1,4,5 (sucf (sucf (sucf (sucf (sucf (zerof)))))) (sucf (sucf (sucf (zerof)))) p = ncom prfNoteq6--1,5 

u_2,0,3,1,4,5 (sucf (sucf (sucf (sucf (zerof))))) (sucf (sucf (sucf (sucf (sucf (zerof)))))) p = prfNoteq6--4,5 
u_2,0,3,1,4,5 (sucf (sucf (sucf (sucf (sucf (zerof)))))) (sucf (sucf (sucf (sucf (zerof))))) p = ncom prfNoteq6--4,5 

u_2,3,0,1,4,5 : (i j : Fin 6) → (i ≢ j) → nth p_2,3,0,1,4,5 i ≢ nth p_2,3,0,1,4,5 j 
u_2,3,0,1,4,5 (zerof) (zerof) p = ⊥-elim (p refl)
u_2,3,0,1,4,5 (sucf (zerof)) (sucf (zerof)) p = ⊥-elim (p refl)
u_2,3,0,1,4,5 (sucf (sucf (zerof))) (sucf (sucf (zerof))) p = ⊥-elim (p refl)
u_2,3,0,1,4,5 (sucf (sucf (sucf (zerof)))) (sucf (sucf (sucf (zerof)))) p = ⊥-elim (p refl)
u_2,3,0,1,4,5 (sucf (sucf (sucf (sucf (zerof))))) (sucf (sucf (sucf (sucf (zerof))))) p = ⊥-elim (p refl)
u_2,3,0,1,4,5 (sucf (sucf (sucf (sucf (sucf (zerof)))))) (sucf (sucf (sucf (sucf (sucf (zerof)))))) p = ⊥-elim (p refl)
u_2,3,0,1,4,5 (sucf (sucf (sucf (sucf (sucf (sucf h)))))) _ = ⊥-elim (nolify h) 
u_2,3,0,1,4,5 _ (sucf (sucf (sucf (sucf (sucf (sucf h)))))) = ⊥-elim (nolify h) 

u_2,3,0,1,4,5 (zerof) (sucf (zerof)) p = prfNoteq6--2,3 
u_2,3,0,1,4,5 (sucf (zerof)) (zerof) p = ncom prfNoteq6--2,3 

u_2,3,0,1,4,5 (zerof) (sucf (sucf (zerof))) p = ncom prfNoteq6--0,2 
u_2,3,0,1,4,5 (sucf (sucf (zerof))) (zerof) p = prfNoteq6--0,2 

u_2,3,0,1,4,5 (zerof) (sucf (sucf (sucf (zerof)))) p = ncom prfNoteq6--1,2 
u_2,3,0,1,4,5 (sucf (sucf (sucf (zerof)))) (zerof) p = prfNoteq6--1,2 

u_2,3,0,1,4,5 (zerof) (sucf (sucf (sucf (sucf (zerof))))) p = prfNoteq6--2,4 
u_2,3,0,1,4,5 (sucf (sucf (sucf (sucf (zerof))))) (zerof) p = ncom prfNoteq6--2,4 

u_2,3,0,1,4,5 (zerof) (sucf (sucf (sucf (sucf (sucf (zerof)))))) p = prfNoteq6--2,5 
u_2,3,0,1,4,5 (sucf (sucf (sucf (sucf (sucf (zerof)))))) (zerof) p = ncom prfNoteq6--2,5 

u_2,3,0,1,4,5 (sucf (zerof)) (sucf (sucf (zerof))) p = ncom prfNoteq6--0,3 
u_2,3,0,1,4,5 (sucf (sucf (zerof))) (sucf (zerof)) p = prfNoteq6--0,3 

u_2,3,0,1,4,5 (sucf (zerof)) (sucf (sucf (sucf (zerof)))) p = ncom prfNoteq6--1,3 
u_2,3,0,1,4,5 (sucf (sucf (sucf (zerof)))) (sucf (zerof)) p = prfNoteq6--1,3 

u_2,3,0,1,4,5 (sucf (zerof)) (sucf (sucf (sucf (sucf (zerof))))) p = prfNoteq6--3,4 
u_2,3,0,1,4,5 (sucf (sucf (sucf (sucf (zerof))))) (sucf (zerof)) p = ncom prfNoteq6--3,4 

u_2,3,0,1,4,5 (sucf (zerof)) (sucf (sucf (sucf (sucf (sucf (zerof)))))) p = prfNoteq6--3,5 
u_2,3,0,1,4,5 (sucf (sucf (sucf (sucf (sucf (zerof)))))) (sucf (zerof)) p = ncom prfNoteq6--3,5 

u_2,3,0,1,4,5 (sucf (sucf (zerof))) (sucf (sucf (sucf (zerof)))) p = prfNoteq6--0,1 
u_2,3,0,1,4,5 (sucf (sucf (sucf (zerof)))) (sucf (sucf (zerof))) p = ncom prfNoteq6--0,1 

u_2,3,0,1,4,5 (sucf (sucf (zerof))) (sucf (sucf (sucf (sucf (zerof))))) p = prfNoteq6--0,4 
u_2,3,0,1,4,5 (sucf (sucf (sucf (sucf (zerof))))) (sucf (sucf (zerof))) p = ncom prfNoteq6--0,4 

u_2,3,0,1,4,5 (sucf (sucf (zerof))) (sucf (sucf (sucf (sucf (sucf (zerof)))))) p = prfNoteq6--0,5 
u_2,3,0,1,4,5 (sucf (sucf (sucf (sucf (sucf (zerof)))))) (sucf (sucf (zerof))) p = ncom prfNoteq6--0,5 

u_2,3,0,1,4,5 (sucf (sucf (sucf (zerof)))) (sucf (sucf (sucf (sucf (zerof))))) p = prfNoteq6--1,4 
u_2,3,0,1,4,5 (sucf (sucf (sucf (sucf (zerof))))) (sucf (sucf (sucf (zerof)))) p = ncom prfNoteq6--1,4 

u_2,3,0,1,4,5 (sucf (sucf (sucf (zerof)))) (sucf (sucf (sucf (sucf (sucf (zerof)))))) p = prfNoteq6--1,5 
u_2,3,0,1,4,5 (sucf (sucf (sucf (sucf (sucf (zerof)))))) (sucf (sucf (sucf (zerof)))) p = ncom prfNoteq6--1,5 

u_2,3,0,1,4,5 (sucf (sucf (sucf (sucf (zerof))))) (sucf (sucf (sucf (sucf (sucf (zerof)))))) p = prfNoteq6--4,5 
u_2,3,0,1,4,5 (sucf (sucf (sucf (sucf (sucf (zerof)))))) (sucf (sucf (sucf (sucf (zerof))))) p = ncom prfNoteq6--4,5 

u_3,0,1,2,4,5 : (i j : Fin 6) → (i ≢ j) → nth p_3,0,1,2,4,5 i ≢ nth p_3,0,1,2,4,5 j 
u_3,0,1,2,4,5 (zerof) (zerof) p = ⊥-elim (p refl)
u_3,0,1,2,4,5 (sucf (zerof)) (sucf (zerof)) p = ⊥-elim (p refl)
u_3,0,1,2,4,5 (sucf (sucf (zerof))) (sucf (sucf (zerof))) p = ⊥-elim (p refl)
u_3,0,1,2,4,5 (sucf (sucf (sucf (zerof)))) (sucf (sucf (sucf (zerof)))) p = ⊥-elim (p refl)
u_3,0,1,2,4,5 (sucf (sucf (sucf (sucf (zerof))))) (sucf (sucf (sucf (sucf (zerof))))) p = ⊥-elim (p refl)
u_3,0,1,2,4,5 (sucf (sucf (sucf (sucf (sucf (zerof)))))) (sucf (sucf (sucf (sucf (sucf (zerof)))))) p = ⊥-elim (p refl)
u_3,0,1,2,4,5 (sucf (sucf (sucf (sucf (sucf (sucf h)))))) _ = ⊥-elim (nolify h) 
u_3,0,1,2,4,5 _ (sucf (sucf (sucf (sucf (sucf (sucf h)))))) = ⊥-elim (nolify h) 

u_3,0,1,2,4,5 (zerof) (sucf (zerof)) p = ncom prfNoteq6--0,3 
u_3,0,1,2,4,5 (sucf (zerof)) (zerof) p = prfNoteq6--0,3 

u_3,0,1,2,4,5 (zerof) (sucf (sucf (zerof))) p = ncom prfNoteq6--1,3 
u_3,0,1,2,4,5 (sucf (sucf (zerof))) (zerof) p = prfNoteq6--1,3 

u_3,0,1,2,4,5 (zerof) (sucf (sucf (sucf (zerof)))) p = ncom prfNoteq6--2,3 
u_3,0,1,2,4,5 (sucf (sucf (sucf (zerof)))) (zerof) p = prfNoteq6--2,3 

u_3,0,1,2,4,5 (zerof) (sucf (sucf (sucf (sucf (zerof))))) p = prfNoteq6--3,4 
u_3,0,1,2,4,5 (sucf (sucf (sucf (sucf (zerof))))) (zerof) p = ncom prfNoteq6--3,4 

u_3,0,1,2,4,5 (zerof) (sucf (sucf (sucf (sucf (sucf (zerof)))))) p = prfNoteq6--3,5 
u_3,0,1,2,4,5 (sucf (sucf (sucf (sucf (sucf (zerof)))))) (zerof) p = ncom prfNoteq6--3,5 

u_3,0,1,2,4,5 (sucf (zerof)) (sucf (sucf (zerof))) p = prfNoteq6--0,1 
u_3,0,1,2,4,5 (sucf (sucf (zerof))) (sucf (zerof)) p = ncom prfNoteq6--0,1 

u_3,0,1,2,4,5 (sucf (zerof)) (sucf (sucf (sucf (zerof)))) p = prfNoteq6--0,2 
u_3,0,1,2,4,5 (sucf (sucf (sucf (zerof)))) (sucf (zerof)) p = ncom prfNoteq6--0,2 

u_3,0,1,2,4,5 (sucf (zerof)) (sucf (sucf (sucf (sucf (zerof))))) p = prfNoteq6--0,4 
u_3,0,1,2,4,5 (sucf (sucf (sucf (sucf (zerof))))) (sucf (zerof)) p = ncom prfNoteq6--0,4 

u_3,0,1,2,4,5 (sucf (zerof)) (sucf (sucf (sucf (sucf (sucf (zerof)))))) p = prfNoteq6--0,5 
u_3,0,1,2,4,5 (sucf (sucf (sucf (sucf (sucf (zerof)))))) (sucf (zerof)) p = ncom prfNoteq6--0,5 

u_3,0,1,2,4,5 (sucf (sucf (zerof))) (sucf (sucf (sucf (zerof)))) p = prfNoteq6--1,2 
u_3,0,1,2,4,5 (sucf (sucf (sucf (zerof)))) (sucf (sucf (zerof))) p = ncom prfNoteq6--1,2 

u_3,0,1,2,4,5 (sucf (sucf (zerof))) (sucf (sucf (sucf (sucf (zerof))))) p = prfNoteq6--1,4 
u_3,0,1,2,4,5 (sucf (sucf (sucf (sucf (zerof))))) (sucf (sucf (zerof))) p = ncom prfNoteq6--1,4 

u_3,0,1,2,4,5 (sucf (sucf (zerof))) (sucf (sucf (sucf (sucf (sucf (zerof)))))) p = prfNoteq6--1,5 
u_3,0,1,2,4,5 (sucf (sucf (sucf (sucf (sucf (zerof)))))) (sucf (sucf (zerof))) p = ncom prfNoteq6--1,5 

u_3,0,1,2,4,5 (sucf (sucf (sucf (zerof)))) (sucf (sucf (sucf (sucf (zerof))))) p = prfNoteq6--2,4 
u_3,0,1,2,4,5 (sucf (sucf (sucf (sucf (zerof))))) (sucf (sucf (sucf (zerof)))) p = ncom prfNoteq6--2,4 

u_3,0,1,2,4,5 (sucf (sucf (sucf (zerof)))) (sucf (sucf (sucf (sucf (sucf (zerof)))))) p = prfNoteq6--2,5 
u_3,0,1,2,4,5 (sucf (sucf (sucf (sucf (sucf (zerof)))))) (sucf (sucf (sucf (zerof)))) p = ncom prfNoteq6--2,5 

u_3,0,1,2,4,5 (sucf (sucf (sucf (sucf (zerof))))) (sucf (sucf (sucf (sucf (sucf (zerof)))))) p = prfNoteq6--4,5 
u_3,0,1,2,4,5 (sucf (sucf (sucf (sucf (sucf (zerof)))))) (sucf (sucf (sucf (sucf (zerof))))) p = ncom prfNoteq6--4,5 

u_3,0,2,1,4,5 : (i j : Fin 6) → (i ≢ j) → nth p_3,0,2,1,4,5 i ≢ nth p_3,0,2,1,4,5 j 
u_3,0,2,1,4,5 (zerof) (zerof) p = ⊥-elim (p refl)
u_3,0,2,1,4,5 (sucf (zerof)) (sucf (zerof)) p = ⊥-elim (p refl)
u_3,0,2,1,4,5 (sucf (sucf (zerof))) (sucf (sucf (zerof))) p = ⊥-elim (p refl)
u_3,0,2,1,4,5 (sucf (sucf (sucf (zerof)))) (sucf (sucf (sucf (zerof)))) p = ⊥-elim (p refl)
u_3,0,2,1,4,5 (sucf (sucf (sucf (sucf (zerof))))) (sucf (sucf (sucf (sucf (zerof))))) p = ⊥-elim (p refl)
u_3,0,2,1,4,5 (sucf (sucf (sucf (sucf (sucf (zerof)))))) (sucf (sucf (sucf (sucf (sucf (zerof)))))) p = ⊥-elim (p refl)
u_3,0,2,1,4,5 (sucf (sucf (sucf (sucf (sucf (sucf h)))))) _ = ⊥-elim (nolify h) 
u_3,0,2,1,4,5 _ (sucf (sucf (sucf (sucf (sucf (sucf h)))))) = ⊥-elim (nolify h) 

u_3,0,2,1,4,5 (zerof) (sucf (zerof)) p = ncom prfNoteq6--0,3 
u_3,0,2,1,4,5 (sucf (zerof)) (zerof) p = prfNoteq6--0,3 

u_3,0,2,1,4,5 (zerof) (sucf (sucf (zerof))) p = ncom prfNoteq6--2,3 
u_3,0,2,1,4,5 (sucf (sucf (zerof))) (zerof) p = prfNoteq6--2,3 

u_3,0,2,1,4,5 (zerof) (sucf (sucf (sucf (zerof)))) p = ncom prfNoteq6--1,3 
u_3,0,2,1,4,5 (sucf (sucf (sucf (zerof)))) (zerof) p = prfNoteq6--1,3 

u_3,0,2,1,4,5 (zerof) (sucf (sucf (sucf (sucf (zerof))))) p = prfNoteq6--3,4 
u_3,0,2,1,4,5 (sucf (sucf (sucf (sucf (zerof))))) (zerof) p = ncom prfNoteq6--3,4 

u_3,0,2,1,4,5 (zerof) (sucf (sucf (sucf (sucf (sucf (zerof)))))) p = prfNoteq6--3,5 
u_3,0,2,1,4,5 (sucf (sucf (sucf (sucf (sucf (zerof)))))) (zerof) p = ncom prfNoteq6--3,5 

u_3,0,2,1,4,5 (sucf (zerof)) (sucf (sucf (zerof))) p = prfNoteq6--0,2 
u_3,0,2,1,4,5 (sucf (sucf (zerof))) (sucf (zerof)) p = ncom prfNoteq6--0,2 

u_3,0,2,1,4,5 (sucf (zerof)) (sucf (sucf (sucf (zerof)))) p = prfNoteq6--0,1 
u_3,0,2,1,4,5 (sucf (sucf (sucf (zerof)))) (sucf (zerof)) p = ncom prfNoteq6--0,1 

u_3,0,2,1,4,5 (sucf (zerof)) (sucf (sucf (sucf (sucf (zerof))))) p = prfNoteq6--0,4 
u_3,0,2,1,4,5 (sucf (sucf (sucf (sucf (zerof))))) (sucf (zerof)) p = ncom prfNoteq6--0,4 

u_3,0,2,1,4,5 (sucf (zerof)) (sucf (sucf (sucf (sucf (sucf (zerof)))))) p = prfNoteq6--0,5 
u_3,0,2,1,4,5 (sucf (sucf (sucf (sucf (sucf (zerof)))))) (sucf (zerof)) p = ncom prfNoteq6--0,5 

u_3,0,2,1,4,5 (sucf (sucf (zerof))) (sucf (sucf (sucf (zerof)))) p = ncom prfNoteq6--1,2 
u_3,0,2,1,4,5 (sucf (sucf (sucf (zerof)))) (sucf (sucf (zerof))) p = prfNoteq6--1,2 

u_3,0,2,1,4,5 (sucf (sucf (zerof))) (sucf (sucf (sucf (sucf (zerof))))) p = prfNoteq6--2,4 
u_3,0,2,1,4,5 (sucf (sucf (sucf (sucf (zerof))))) (sucf (sucf (zerof))) p = ncom prfNoteq6--2,4 

u_3,0,2,1,4,5 (sucf (sucf (zerof))) (sucf (sucf (sucf (sucf (sucf (zerof)))))) p = prfNoteq6--2,5 
u_3,0,2,1,4,5 (sucf (sucf (sucf (sucf (sucf (zerof)))))) (sucf (sucf (zerof))) p = ncom prfNoteq6--2,5 

u_3,0,2,1,4,5 (sucf (sucf (sucf (zerof)))) (sucf (sucf (sucf (sucf (zerof))))) p = prfNoteq6--1,4 
u_3,0,2,1,4,5 (sucf (sucf (sucf (sucf (zerof))))) (sucf (sucf (sucf (zerof)))) p = ncom prfNoteq6--1,4 

u_3,0,2,1,4,5 (sucf (sucf (sucf (zerof)))) (sucf (sucf (sucf (sucf (sucf (zerof)))))) p = prfNoteq6--1,5 
u_3,0,2,1,4,5 (sucf (sucf (sucf (sucf (sucf (zerof)))))) (sucf (sucf (sucf (zerof)))) p = ncom prfNoteq6--1,5 

u_3,0,2,1,4,5 (sucf (sucf (sucf (sucf (zerof))))) (sucf (sucf (sucf (sucf (sucf (zerof)))))) p = prfNoteq6--4,5 
u_3,0,2,1,4,5 (sucf (sucf (sucf (sucf (sucf (zerof)))))) (sucf (sucf (sucf (sucf (zerof))))) p = ncom prfNoteq6--4,5 

u_3,1,0,2,4,5 : (i j : Fin 6) → (i ≢ j) → nth p_3,1,0,2,4,5 i ≢ nth p_3,1,0,2,4,5 j 
u_3,1,0,2,4,5 (zerof) (zerof) p = ⊥-elim (p refl)
u_3,1,0,2,4,5 (sucf (zerof)) (sucf (zerof)) p = ⊥-elim (p refl)
u_3,1,0,2,4,5 (sucf (sucf (zerof))) (sucf (sucf (zerof))) p = ⊥-elim (p refl)
u_3,1,0,2,4,5 (sucf (sucf (sucf (zerof)))) (sucf (sucf (sucf (zerof)))) p = ⊥-elim (p refl)
u_3,1,0,2,4,5 (sucf (sucf (sucf (sucf (zerof))))) (sucf (sucf (sucf (sucf (zerof))))) p = ⊥-elim (p refl)
u_3,1,0,2,4,5 (sucf (sucf (sucf (sucf (sucf (zerof)))))) (sucf (sucf (sucf (sucf (sucf (zerof)))))) p = ⊥-elim (p refl)
u_3,1,0,2,4,5 (sucf (sucf (sucf (sucf (sucf (sucf h)))))) _ = ⊥-elim (nolify h) 
u_3,1,0,2,4,5 _ (sucf (sucf (sucf (sucf (sucf (sucf h)))))) = ⊥-elim (nolify h) 

u_3,1,0,2,4,5 (zerof) (sucf (zerof)) p = ncom prfNoteq6--1,3 
u_3,1,0,2,4,5 (sucf (zerof)) (zerof) p = prfNoteq6--1,3 

u_3,1,0,2,4,5 (zerof) (sucf (sucf (zerof))) p = ncom prfNoteq6--0,3 
u_3,1,0,2,4,5 (sucf (sucf (zerof))) (zerof) p = prfNoteq6--0,3 

u_3,1,0,2,4,5 (zerof) (sucf (sucf (sucf (zerof)))) p = ncom prfNoteq6--2,3 
u_3,1,0,2,4,5 (sucf (sucf (sucf (zerof)))) (zerof) p = prfNoteq6--2,3 

u_3,1,0,2,4,5 (zerof) (sucf (sucf (sucf (sucf (zerof))))) p = prfNoteq6--3,4 
u_3,1,0,2,4,5 (sucf (sucf (sucf (sucf (zerof))))) (zerof) p = ncom prfNoteq6--3,4 

u_3,1,0,2,4,5 (zerof) (sucf (sucf (sucf (sucf (sucf (zerof)))))) p = prfNoteq6--3,5 
u_3,1,0,2,4,5 (sucf (sucf (sucf (sucf (sucf (zerof)))))) (zerof) p = ncom prfNoteq6--3,5 

u_3,1,0,2,4,5 (sucf (zerof)) (sucf (sucf (zerof))) p = ncom prfNoteq6--0,1 
u_3,1,0,2,4,5 (sucf (sucf (zerof))) (sucf (zerof)) p = prfNoteq6--0,1 

u_3,1,0,2,4,5 (sucf (zerof)) (sucf (sucf (sucf (zerof)))) p = prfNoteq6--1,2 
u_3,1,0,2,4,5 (sucf (sucf (sucf (zerof)))) (sucf (zerof)) p = ncom prfNoteq6--1,2 

u_3,1,0,2,4,5 (sucf (zerof)) (sucf (sucf (sucf (sucf (zerof))))) p = prfNoteq6--1,4 
u_3,1,0,2,4,5 (sucf (sucf (sucf (sucf (zerof))))) (sucf (zerof)) p = ncom prfNoteq6--1,4 

u_3,1,0,2,4,5 (sucf (zerof)) (sucf (sucf (sucf (sucf (sucf (zerof)))))) p = prfNoteq6--1,5 
u_3,1,0,2,4,5 (sucf (sucf (sucf (sucf (sucf (zerof)))))) (sucf (zerof)) p = ncom prfNoteq6--1,5 

u_3,1,0,2,4,5 (sucf (sucf (zerof))) (sucf (sucf (sucf (zerof)))) p = prfNoteq6--0,2 
u_3,1,0,2,4,5 (sucf (sucf (sucf (zerof)))) (sucf (sucf (zerof))) p = ncom prfNoteq6--0,2 

u_3,1,0,2,4,5 (sucf (sucf (zerof))) (sucf (sucf (sucf (sucf (zerof))))) p = prfNoteq6--0,4 
u_3,1,0,2,4,5 (sucf (sucf (sucf (sucf (zerof))))) (sucf (sucf (zerof))) p = ncom prfNoteq6--0,4 

u_3,1,0,2,4,5 (sucf (sucf (zerof))) (sucf (sucf (sucf (sucf (sucf (zerof)))))) p = prfNoteq6--0,5 
u_3,1,0,2,4,5 (sucf (sucf (sucf (sucf (sucf (zerof)))))) (sucf (sucf (zerof))) p = ncom prfNoteq6--0,5 

u_3,1,0,2,4,5 (sucf (sucf (sucf (zerof)))) (sucf (sucf (sucf (sucf (zerof))))) p = prfNoteq6--2,4 
u_3,1,0,2,4,5 (sucf (sucf (sucf (sucf (zerof))))) (sucf (sucf (sucf (zerof)))) p = ncom prfNoteq6--2,4 

u_3,1,0,2,4,5 (sucf (sucf (sucf (zerof)))) (sucf (sucf (sucf (sucf (sucf (zerof)))))) p = prfNoteq6--2,5 
u_3,1,0,2,4,5 (sucf (sucf (sucf (sucf (sucf (zerof)))))) (sucf (sucf (sucf (zerof)))) p = ncom prfNoteq6--2,5 

u_3,1,0,2,4,5 (sucf (sucf (sucf (sucf (zerof))))) (sucf (sucf (sucf (sucf (sucf (zerof)))))) p = prfNoteq6--4,5 
u_3,1,0,2,4,5 (sucf (sucf (sucf (sucf (sucf (zerof)))))) (sucf (sucf (sucf (sucf (zerof))))) p = ncom prfNoteq6--4,5 

u_3,1,2,0,4,5 : (i j : Fin 6) → (i ≢ j) → nth p_3,1,2,0,4,5 i ≢ nth p_3,1,2,0,4,5 j 
u_3,1,2,0,4,5 (zerof) (zerof) p = ⊥-elim (p refl)
u_3,1,2,0,4,5 (sucf (zerof)) (sucf (zerof)) p = ⊥-elim (p refl)
u_3,1,2,0,4,5 (sucf (sucf (zerof))) (sucf (sucf (zerof))) p = ⊥-elim (p refl)
u_3,1,2,0,4,5 (sucf (sucf (sucf (zerof)))) (sucf (sucf (sucf (zerof)))) p = ⊥-elim (p refl)
u_3,1,2,0,4,5 (sucf (sucf (sucf (sucf (zerof))))) (sucf (sucf (sucf (sucf (zerof))))) p = ⊥-elim (p refl)
u_3,1,2,0,4,5 (sucf (sucf (sucf (sucf (sucf (zerof)))))) (sucf (sucf (sucf (sucf (sucf (zerof)))))) p = ⊥-elim (p refl)
u_3,1,2,0,4,5 (sucf (sucf (sucf (sucf (sucf (sucf h)))))) _ = ⊥-elim (nolify h) 
u_3,1,2,0,4,5 _ (sucf (sucf (sucf (sucf (sucf (sucf h)))))) = ⊥-elim (nolify h) 

u_3,1,2,0,4,5 (zerof) (sucf (zerof)) p = ncom prfNoteq6--1,3 
u_3,1,2,0,4,5 (sucf (zerof)) (zerof) p = prfNoteq6--1,3 

u_3,1,2,0,4,5 (zerof) (sucf (sucf (zerof))) p = ncom prfNoteq6--2,3 
u_3,1,2,0,4,5 (sucf (sucf (zerof))) (zerof) p = prfNoteq6--2,3 

u_3,1,2,0,4,5 (zerof) (sucf (sucf (sucf (zerof)))) p = ncom prfNoteq6--0,3 
u_3,1,2,0,4,5 (sucf (sucf (sucf (zerof)))) (zerof) p = prfNoteq6--0,3 

u_3,1,2,0,4,5 (zerof) (sucf (sucf (sucf (sucf (zerof))))) p = prfNoteq6--3,4 
u_3,1,2,0,4,5 (sucf (sucf (sucf (sucf (zerof))))) (zerof) p = ncom prfNoteq6--3,4 

u_3,1,2,0,4,5 (zerof) (sucf (sucf (sucf (sucf (sucf (zerof)))))) p = prfNoteq6--3,5 
u_3,1,2,0,4,5 (sucf (sucf (sucf (sucf (sucf (zerof)))))) (zerof) p = ncom prfNoteq6--3,5 

u_3,1,2,0,4,5 (sucf (zerof)) (sucf (sucf (zerof))) p = prfNoteq6--1,2 
u_3,1,2,0,4,5 (sucf (sucf (zerof))) (sucf (zerof)) p = ncom prfNoteq6--1,2 

u_3,1,2,0,4,5 (sucf (zerof)) (sucf (sucf (sucf (zerof)))) p = ncom prfNoteq6--0,1 
u_3,1,2,0,4,5 (sucf (sucf (sucf (zerof)))) (sucf (zerof)) p = prfNoteq6--0,1 

u_3,1,2,0,4,5 (sucf (zerof)) (sucf (sucf (sucf (sucf (zerof))))) p = prfNoteq6--1,4 
u_3,1,2,0,4,5 (sucf (sucf (sucf (sucf (zerof))))) (sucf (zerof)) p = ncom prfNoteq6--1,4 

u_3,1,2,0,4,5 (sucf (zerof)) (sucf (sucf (sucf (sucf (sucf (zerof)))))) p = prfNoteq6--1,5 
u_3,1,2,0,4,5 (sucf (sucf (sucf (sucf (sucf (zerof)))))) (sucf (zerof)) p = ncom prfNoteq6--1,5 

u_3,1,2,0,4,5 (sucf (sucf (zerof))) (sucf (sucf (sucf (zerof)))) p = ncom prfNoteq6--0,2 
u_3,1,2,0,4,5 (sucf (sucf (sucf (zerof)))) (sucf (sucf (zerof))) p = prfNoteq6--0,2 

u_3,1,2,0,4,5 (sucf (sucf (zerof))) (sucf (sucf (sucf (sucf (zerof))))) p = prfNoteq6--2,4 
u_3,1,2,0,4,5 (sucf (sucf (sucf (sucf (zerof))))) (sucf (sucf (zerof))) p = ncom prfNoteq6--2,4 

u_3,1,2,0,4,5 (sucf (sucf (zerof))) (sucf (sucf (sucf (sucf (sucf (zerof)))))) p = prfNoteq6--2,5 
u_3,1,2,0,4,5 (sucf (sucf (sucf (sucf (sucf (zerof)))))) (sucf (sucf (zerof))) p = ncom prfNoteq6--2,5 

u_3,1,2,0,4,5 (sucf (sucf (sucf (zerof)))) (sucf (sucf (sucf (sucf (zerof))))) p = prfNoteq6--0,4 
u_3,1,2,0,4,5 (sucf (sucf (sucf (sucf (zerof))))) (sucf (sucf (sucf (zerof)))) p = ncom prfNoteq6--0,4 

u_3,1,2,0,4,5 (sucf (sucf (sucf (zerof)))) (sucf (sucf (sucf (sucf (sucf (zerof)))))) p = prfNoteq6--0,5 
u_3,1,2,0,4,5 (sucf (sucf (sucf (sucf (sucf (zerof)))))) (sucf (sucf (sucf (zerof)))) p = ncom prfNoteq6--0,5 

u_3,1,2,0,4,5 (sucf (sucf (sucf (sucf (zerof))))) (sucf (sucf (sucf (sucf (sucf (zerof)))))) p = prfNoteq6--4,5 
u_3,1,2,0,4,5 (sucf (sucf (sucf (sucf (sucf (zerof)))))) (sucf (sucf (sucf (sucf (zerof))))) p = ncom prfNoteq6--4,5 

u_3,2,0,1,4,5 : (i j : Fin 6) → (i ≢ j) → nth p_3,2,0,1,4,5 i ≢ nth p_3,2,0,1,4,5 j 
u_3,2,0,1,4,5 (zerof) (zerof) p = ⊥-elim (p refl)
u_3,2,0,1,4,5 (sucf (zerof)) (sucf (zerof)) p = ⊥-elim (p refl)
u_3,2,0,1,4,5 (sucf (sucf (zerof))) (sucf (sucf (zerof))) p = ⊥-elim (p refl)
u_3,2,0,1,4,5 (sucf (sucf (sucf (zerof)))) (sucf (sucf (sucf (zerof)))) p = ⊥-elim (p refl)
u_3,2,0,1,4,5 (sucf (sucf (sucf (sucf (zerof))))) (sucf (sucf (sucf (sucf (zerof))))) p = ⊥-elim (p refl)
u_3,2,0,1,4,5 (sucf (sucf (sucf (sucf (sucf (zerof)))))) (sucf (sucf (sucf (sucf (sucf (zerof)))))) p = ⊥-elim (p refl)
u_3,2,0,1,4,5 (sucf (sucf (sucf (sucf (sucf (sucf h)))))) _ = ⊥-elim (nolify h) 
u_3,2,0,1,4,5 _ (sucf (sucf (sucf (sucf (sucf (sucf h)))))) = ⊥-elim (nolify h) 

u_3,2,0,1,4,5 (zerof) (sucf (zerof)) p = ncom prfNoteq6--2,3 
u_3,2,0,1,4,5 (sucf (zerof)) (zerof) p = prfNoteq6--2,3 

u_3,2,0,1,4,5 (zerof) (sucf (sucf (zerof))) p = ncom prfNoteq6--0,3 
u_3,2,0,1,4,5 (sucf (sucf (zerof))) (zerof) p = prfNoteq6--0,3 

u_3,2,0,1,4,5 (zerof) (sucf (sucf (sucf (zerof)))) p = ncom prfNoteq6--1,3 
u_3,2,0,1,4,5 (sucf (sucf (sucf (zerof)))) (zerof) p = prfNoteq6--1,3 

u_3,2,0,1,4,5 (zerof) (sucf (sucf (sucf (sucf (zerof))))) p = prfNoteq6--3,4 
u_3,2,0,1,4,5 (sucf (sucf (sucf (sucf (zerof))))) (zerof) p = ncom prfNoteq6--3,4 

u_3,2,0,1,4,5 (zerof) (sucf (sucf (sucf (sucf (sucf (zerof)))))) p = prfNoteq6--3,5 
u_3,2,0,1,4,5 (sucf (sucf (sucf (sucf (sucf (zerof)))))) (zerof) p = ncom prfNoteq6--3,5 

u_3,2,0,1,4,5 (sucf (zerof)) (sucf (sucf (zerof))) p = ncom prfNoteq6--0,2 
u_3,2,0,1,4,5 (sucf (sucf (zerof))) (sucf (zerof)) p = prfNoteq6--0,2 

u_3,2,0,1,4,5 (sucf (zerof)) (sucf (sucf (sucf (zerof)))) p = ncom prfNoteq6--1,2 
u_3,2,0,1,4,5 (sucf (sucf (sucf (zerof)))) (sucf (zerof)) p = prfNoteq6--1,2 

u_3,2,0,1,4,5 (sucf (zerof)) (sucf (sucf (sucf (sucf (zerof))))) p = prfNoteq6--2,4 
u_3,2,0,1,4,5 (sucf (sucf (sucf (sucf (zerof))))) (sucf (zerof)) p = ncom prfNoteq6--2,4 

u_3,2,0,1,4,5 (sucf (zerof)) (sucf (sucf (sucf (sucf (sucf (zerof)))))) p = prfNoteq6--2,5 
u_3,2,0,1,4,5 (sucf (sucf (sucf (sucf (sucf (zerof)))))) (sucf (zerof)) p = ncom prfNoteq6--2,5 

u_3,2,0,1,4,5 (sucf (sucf (zerof))) (sucf (sucf (sucf (zerof)))) p = prfNoteq6--0,1 
u_3,2,0,1,4,5 (sucf (sucf (sucf (zerof)))) (sucf (sucf (zerof))) p = ncom prfNoteq6--0,1 

u_3,2,0,1,4,5 (sucf (sucf (zerof))) (sucf (sucf (sucf (sucf (zerof))))) p = prfNoteq6--0,4 
u_3,2,0,1,4,5 (sucf (sucf (sucf (sucf (zerof))))) (sucf (sucf (zerof))) p = ncom prfNoteq6--0,4 

u_3,2,0,1,4,5 (sucf (sucf (zerof))) (sucf (sucf (sucf (sucf (sucf (zerof)))))) p = prfNoteq6--0,5 
u_3,2,0,1,4,5 (sucf (sucf (sucf (sucf (sucf (zerof)))))) (sucf (sucf (zerof))) p = ncom prfNoteq6--0,5 

u_3,2,0,1,4,5 (sucf (sucf (sucf (zerof)))) (sucf (sucf (sucf (sucf (zerof))))) p = prfNoteq6--1,4 
u_3,2,0,1,4,5 (sucf (sucf (sucf (sucf (zerof))))) (sucf (sucf (sucf (zerof)))) p = ncom prfNoteq6--1,4 

u_3,2,0,1,4,5 (sucf (sucf (sucf (zerof)))) (sucf (sucf (sucf (sucf (sucf (zerof)))))) p = prfNoteq6--1,5 
u_3,2,0,1,4,5 (sucf (sucf (sucf (sucf (sucf (zerof)))))) (sucf (sucf (sucf (zerof)))) p = ncom prfNoteq6--1,5 

u_3,2,0,1,4,5 (sucf (sucf (sucf (sucf (zerof))))) (sucf (sucf (sucf (sucf (sucf (zerof)))))) p = prfNoteq6--4,5 
u_3,2,0,1,4,5 (sucf (sucf (sucf (sucf (sucf (zerof)))))) (sucf (sucf (sucf (sucf (zerof))))) p = ncom prfNoteq6--4,5 

u_3,2,1,0,4,5 : (i j : Fin 6) → (i ≢ j) → nth p_3,2,1,0,4,5 i ≢ nth p_3,2,1,0,4,5 j 
u_3,2,1,0,4,5 (zerof) (zerof) p = ⊥-elim (p refl)
u_3,2,1,0,4,5 (sucf (zerof)) (sucf (zerof)) p = ⊥-elim (p refl)
u_3,2,1,0,4,5 (sucf (sucf (zerof))) (sucf (sucf (zerof))) p = ⊥-elim (p refl)
u_3,2,1,0,4,5 (sucf (sucf (sucf (zerof)))) (sucf (sucf (sucf (zerof)))) p = ⊥-elim (p refl)
u_3,2,1,0,4,5 (sucf (sucf (sucf (sucf (zerof))))) (sucf (sucf (sucf (sucf (zerof))))) p = ⊥-elim (p refl)
u_3,2,1,0,4,5 (sucf (sucf (sucf (sucf (sucf (zerof)))))) (sucf (sucf (sucf (sucf (sucf (zerof)))))) p = ⊥-elim (p refl)
u_3,2,1,0,4,5 (sucf (sucf (sucf (sucf (sucf (sucf h)))))) _ = ⊥-elim (nolify h) 
u_3,2,1,0,4,5 _ (sucf (sucf (sucf (sucf (sucf (sucf h)))))) = ⊥-elim (nolify h) 

u_3,2,1,0,4,5 (zerof) (sucf (zerof)) p = ncom prfNoteq6--2,3 
u_3,2,1,0,4,5 (sucf (zerof)) (zerof) p = prfNoteq6--2,3 

u_3,2,1,0,4,5 (zerof) (sucf (sucf (zerof))) p = ncom prfNoteq6--1,3 
u_3,2,1,0,4,5 (sucf (sucf (zerof))) (zerof) p = prfNoteq6--1,3 

u_3,2,1,0,4,5 (zerof) (sucf (sucf (sucf (zerof)))) p = ncom prfNoteq6--0,3 
u_3,2,1,0,4,5 (sucf (sucf (sucf (zerof)))) (zerof) p = prfNoteq6--0,3 

u_3,2,1,0,4,5 (zerof) (sucf (sucf (sucf (sucf (zerof))))) p = prfNoteq6--3,4 
u_3,2,1,0,4,5 (sucf (sucf (sucf (sucf (zerof))))) (zerof) p = ncom prfNoteq6--3,4 

u_3,2,1,0,4,5 (zerof) (sucf (sucf (sucf (sucf (sucf (zerof)))))) p = prfNoteq6--3,5 
u_3,2,1,0,4,5 (sucf (sucf (sucf (sucf (sucf (zerof)))))) (zerof) p = ncom prfNoteq6--3,5 

u_3,2,1,0,4,5 (sucf (zerof)) (sucf (sucf (zerof))) p = ncom prfNoteq6--1,2 
u_3,2,1,0,4,5 (sucf (sucf (zerof))) (sucf (zerof)) p = prfNoteq6--1,2 

u_3,2,1,0,4,5 (sucf (zerof)) (sucf (sucf (sucf (zerof)))) p = ncom prfNoteq6--0,2 
u_3,2,1,0,4,5 (sucf (sucf (sucf (zerof)))) (sucf (zerof)) p = prfNoteq6--0,2 

u_3,2,1,0,4,5 (sucf (zerof)) (sucf (sucf (sucf (sucf (zerof))))) p = prfNoteq6--2,4 
u_3,2,1,0,4,5 (sucf (sucf (sucf (sucf (zerof))))) (sucf (zerof)) p = ncom prfNoteq6--2,4 

u_3,2,1,0,4,5 (sucf (zerof)) (sucf (sucf (sucf (sucf (sucf (zerof)))))) p = prfNoteq6--2,5 
u_3,2,1,0,4,5 (sucf (sucf (sucf (sucf (sucf (zerof)))))) (sucf (zerof)) p = ncom prfNoteq6--2,5 

u_3,2,1,0,4,5 (sucf (sucf (zerof))) (sucf (sucf (sucf (zerof)))) p = ncom prfNoteq6--0,1 
u_3,2,1,0,4,5 (sucf (sucf (sucf (zerof)))) (sucf (sucf (zerof))) p = prfNoteq6--0,1 

u_3,2,1,0,4,5 (sucf (sucf (zerof))) (sucf (sucf (sucf (sucf (zerof))))) p = prfNoteq6--1,4 
u_3,2,1,0,4,5 (sucf (sucf (sucf (sucf (zerof))))) (sucf (sucf (zerof))) p = ncom prfNoteq6--1,4 

u_3,2,1,0,4,5 (sucf (sucf (zerof))) (sucf (sucf (sucf (sucf (sucf (zerof)))))) p = prfNoteq6--1,5 
u_3,2,1,0,4,5 (sucf (sucf (sucf (sucf (sucf (zerof)))))) (sucf (sucf (zerof))) p = ncom prfNoteq6--1,5 

u_3,2,1,0,4,5 (sucf (sucf (sucf (zerof)))) (sucf (sucf (sucf (sucf (zerof))))) p = prfNoteq6--0,4 
u_3,2,1,0,4,5 (sucf (sucf (sucf (sucf (zerof))))) (sucf (sucf (sucf (zerof)))) p = ncom prfNoteq6--0,4 

u_3,2,1,0,4,5 (sucf (sucf (sucf (zerof)))) (sucf (sucf (sucf (sucf (sucf (zerof)))))) p = prfNoteq6--0,5 
u_3,2,1,0,4,5 (sucf (sucf (sucf (sucf (sucf (zerof)))))) (sucf (sucf (sucf (zerof)))) p = ncom prfNoteq6--0,5 

u_3,2,1,0,4,5 (sucf (sucf (sucf (sucf (zerof))))) (sucf (sucf (sucf (sucf (sucf (zerof)))))) p = prfNoteq6--4,5 
u_3,2,1,0,4,5 (sucf (sucf (sucf (sucf (sucf (zerof)))))) (sucf (sucf (sucf (sucf (zerof))))) p = ncom prfNoteq6--4,5 

u_0,1,2,3,5,4 : (i j : Fin 6) → (i ≢ j) → nth p_0,1,2,3,5,4 i ≢ nth p_0,1,2,3,5,4 j 
u_0,1,2,3,5,4 (zerof) (zerof) p = ⊥-elim (p refl)
u_0,1,2,3,5,4 (sucf (zerof)) (sucf (zerof)) p = ⊥-elim (p refl)
u_0,1,2,3,5,4 (sucf (sucf (zerof))) (sucf (sucf (zerof))) p = ⊥-elim (p refl)
u_0,1,2,3,5,4 (sucf (sucf (sucf (zerof)))) (sucf (sucf (sucf (zerof)))) p = ⊥-elim (p refl)
u_0,1,2,3,5,4 (sucf (sucf (sucf (sucf (zerof))))) (sucf (sucf (sucf (sucf (zerof))))) p = ⊥-elim (p refl)
u_0,1,2,3,5,4 (sucf (sucf (sucf (sucf (sucf (zerof)))))) (sucf (sucf (sucf (sucf (sucf (zerof)))))) p = ⊥-elim (p refl)
u_0,1,2,3,5,4 (sucf (sucf (sucf (sucf (sucf (sucf h)))))) _ = ⊥-elim (nolify h) 
u_0,1,2,3,5,4 _ (sucf (sucf (sucf (sucf (sucf (sucf h)))))) = ⊥-elim (nolify h) 

u_0,1,2,3,5,4 (zerof) (sucf (zerof)) p = prfNoteq6--0,1 
u_0,1,2,3,5,4 (sucf (zerof)) (zerof) p = ncom prfNoteq6--0,1 

u_0,1,2,3,5,4 (zerof) (sucf (sucf (zerof))) p = prfNoteq6--0,2 
u_0,1,2,3,5,4 (sucf (sucf (zerof))) (zerof) p = ncom prfNoteq6--0,2 

u_0,1,2,3,5,4 (zerof) (sucf (sucf (sucf (zerof)))) p = prfNoteq6--0,3 
u_0,1,2,3,5,4 (sucf (sucf (sucf (zerof)))) (zerof) p = ncom prfNoteq6--0,3 

u_0,1,2,3,5,4 (zerof) (sucf (sucf (sucf (sucf (zerof))))) p = prfNoteq6--0,5 
u_0,1,2,3,5,4 (sucf (sucf (sucf (sucf (zerof))))) (zerof) p = ncom prfNoteq6--0,5 

u_0,1,2,3,5,4 (zerof) (sucf (sucf (sucf (sucf (sucf (zerof)))))) p = prfNoteq6--0,4 
u_0,1,2,3,5,4 (sucf (sucf (sucf (sucf (sucf (zerof)))))) (zerof) p = ncom prfNoteq6--0,4 

u_0,1,2,3,5,4 (sucf (zerof)) (sucf (sucf (zerof))) p = prfNoteq6--1,2 
u_0,1,2,3,5,4 (sucf (sucf (zerof))) (sucf (zerof)) p = ncom prfNoteq6--1,2 

u_0,1,2,3,5,4 (sucf (zerof)) (sucf (sucf (sucf (zerof)))) p = prfNoteq6--1,3 
u_0,1,2,3,5,4 (sucf (sucf (sucf (zerof)))) (sucf (zerof)) p = ncom prfNoteq6--1,3 

u_0,1,2,3,5,4 (sucf (zerof)) (sucf (sucf (sucf (sucf (zerof))))) p = prfNoteq6--1,5 
u_0,1,2,3,5,4 (sucf (sucf (sucf (sucf (zerof))))) (sucf (zerof)) p = ncom prfNoteq6--1,5 

u_0,1,2,3,5,4 (sucf (zerof)) (sucf (sucf (sucf (sucf (sucf (zerof)))))) p = prfNoteq6--1,4 
u_0,1,2,3,5,4 (sucf (sucf (sucf (sucf (sucf (zerof)))))) (sucf (zerof)) p = ncom prfNoteq6--1,4 

u_0,1,2,3,5,4 (sucf (sucf (zerof))) (sucf (sucf (sucf (zerof)))) p = prfNoteq6--2,3 
u_0,1,2,3,5,4 (sucf (sucf (sucf (zerof)))) (sucf (sucf (zerof))) p = ncom prfNoteq6--2,3 

u_0,1,2,3,5,4 (sucf (sucf (zerof))) (sucf (sucf (sucf (sucf (zerof))))) p = prfNoteq6--2,5 
u_0,1,2,3,5,4 (sucf (sucf (sucf (sucf (zerof))))) (sucf (sucf (zerof))) p = ncom prfNoteq6--2,5 

u_0,1,2,3,5,4 (sucf (sucf (zerof))) (sucf (sucf (sucf (sucf (sucf (zerof)))))) p = prfNoteq6--2,4 
u_0,1,2,3,5,4 (sucf (sucf (sucf (sucf (sucf (zerof)))))) (sucf (sucf (zerof))) p = ncom prfNoteq6--2,4 

u_0,1,2,3,5,4 (sucf (sucf (sucf (zerof)))) (sucf (sucf (sucf (sucf (zerof))))) p = prfNoteq6--3,5 
u_0,1,2,3,5,4 (sucf (sucf (sucf (sucf (zerof))))) (sucf (sucf (sucf (zerof)))) p = ncom prfNoteq6--3,5 

u_0,1,2,3,5,4 (sucf (sucf (sucf (zerof)))) (sucf (sucf (sucf (sucf (sucf (zerof)))))) p = prfNoteq6--3,4 
u_0,1,2,3,5,4 (sucf (sucf (sucf (sucf (sucf (zerof)))))) (sucf (sucf (sucf (zerof)))) p = ncom prfNoteq6--3,4 

u_0,1,2,3,5,4 (sucf (sucf (sucf (sucf (zerof))))) (sucf (sucf (sucf (sucf (sucf (zerof)))))) p = ncom prfNoteq6--4,5 
u_0,1,2,3,5,4 (sucf (sucf (sucf (sucf (sucf (zerof)))))) (sucf (sucf (sucf (sucf (zerof))))) p = prfNoteq6--4,5 

u_1,0,2,3,5,4 : (i j : Fin 6) → (i ≢ j) → nth p_1,0,2,3,5,4 i ≢ nth p_1,0,2,3,5,4 j 
u_1,0,2,3,5,4 (zerof) (zerof) p = ⊥-elim (p refl)
u_1,0,2,3,5,4 (sucf (zerof)) (sucf (zerof)) p = ⊥-elim (p refl)
u_1,0,2,3,5,4 (sucf (sucf (zerof))) (sucf (sucf (zerof))) p = ⊥-elim (p refl)
u_1,0,2,3,5,4 (sucf (sucf (sucf (zerof)))) (sucf (sucf (sucf (zerof)))) p = ⊥-elim (p refl)
u_1,0,2,3,5,4 (sucf (sucf (sucf (sucf (zerof))))) (sucf (sucf (sucf (sucf (zerof))))) p = ⊥-elim (p refl)
u_1,0,2,3,5,4 (sucf (sucf (sucf (sucf (sucf (zerof)))))) (sucf (sucf (sucf (sucf (sucf (zerof)))))) p = ⊥-elim (p refl)
u_1,0,2,3,5,4 (sucf (sucf (sucf (sucf (sucf (sucf h)))))) _ = ⊥-elim (nolify h) 
u_1,0,2,3,5,4 _ (sucf (sucf (sucf (sucf (sucf (sucf h)))))) = ⊥-elim (nolify h) 

u_1,0,2,3,5,4 (zerof) (sucf (zerof)) p = ncom prfNoteq6--0,1 
u_1,0,2,3,5,4 (sucf (zerof)) (zerof) p = prfNoteq6--0,1 

u_1,0,2,3,5,4 (zerof) (sucf (sucf (zerof))) p = prfNoteq6--1,2 
u_1,0,2,3,5,4 (sucf (sucf (zerof))) (zerof) p = ncom prfNoteq6--1,2 

u_1,0,2,3,5,4 (zerof) (sucf (sucf (sucf (zerof)))) p = prfNoteq6--1,3 
u_1,0,2,3,5,4 (sucf (sucf (sucf (zerof)))) (zerof) p = ncom prfNoteq6--1,3 

u_1,0,2,3,5,4 (zerof) (sucf (sucf (sucf (sucf (zerof))))) p = prfNoteq6--1,5 
u_1,0,2,3,5,4 (sucf (sucf (sucf (sucf (zerof))))) (zerof) p = ncom prfNoteq6--1,5 

u_1,0,2,3,5,4 (zerof) (sucf (sucf (sucf (sucf (sucf (zerof)))))) p = prfNoteq6--1,4 
u_1,0,2,3,5,4 (sucf (sucf (sucf (sucf (sucf (zerof)))))) (zerof) p = ncom prfNoteq6--1,4 

u_1,0,2,3,5,4 (sucf (zerof)) (sucf (sucf (zerof))) p = prfNoteq6--0,2 
u_1,0,2,3,5,4 (sucf (sucf (zerof))) (sucf (zerof)) p = ncom prfNoteq6--0,2 

u_1,0,2,3,5,4 (sucf (zerof)) (sucf (sucf (sucf (zerof)))) p = prfNoteq6--0,3 
u_1,0,2,3,5,4 (sucf (sucf (sucf (zerof)))) (sucf (zerof)) p = ncom prfNoteq6--0,3 

u_1,0,2,3,5,4 (sucf (zerof)) (sucf (sucf (sucf (sucf (zerof))))) p = prfNoteq6--0,5 
u_1,0,2,3,5,4 (sucf (sucf (sucf (sucf (zerof))))) (sucf (zerof)) p = ncom prfNoteq6--0,5 

u_1,0,2,3,5,4 (sucf (zerof)) (sucf (sucf (sucf (sucf (sucf (zerof)))))) p = prfNoteq6--0,4 
u_1,0,2,3,5,4 (sucf (sucf (sucf (sucf (sucf (zerof)))))) (sucf (zerof)) p = ncom prfNoteq6--0,4 

u_1,0,2,3,5,4 (sucf (sucf (zerof))) (sucf (sucf (sucf (zerof)))) p = prfNoteq6--2,3 
u_1,0,2,3,5,4 (sucf (sucf (sucf (zerof)))) (sucf (sucf (zerof))) p = ncom prfNoteq6--2,3 

u_1,0,2,3,5,4 (sucf (sucf (zerof))) (sucf (sucf (sucf (sucf (zerof))))) p = prfNoteq6--2,5 
u_1,0,2,3,5,4 (sucf (sucf (sucf (sucf (zerof))))) (sucf (sucf (zerof))) p = ncom prfNoteq6--2,5 

u_1,0,2,3,5,4 (sucf (sucf (zerof))) (sucf (sucf (sucf (sucf (sucf (zerof)))))) p = prfNoteq6--2,4 
u_1,0,2,3,5,4 (sucf (sucf (sucf (sucf (sucf (zerof)))))) (sucf (sucf (zerof))) p = ncom prfNoteq6--2,4 

u_1,0,2,3,5,4 (sucf (sucf (sucf (zerof)))) (sucf (sucf (sucf (sucf (zerof))))) p = prfNoteq6--3,5 
u_1,0,2,3,5,4 (sucf (sucf (sucf (sucf (zerof))))) (sucf (sucf (sucf (zerof)))) p = ncom prfNoteq6--3,5 

u_1,0,2,3,5,4 (sucf (sucf (sucf (zerof)))) (sucf (sucf (sucf (sucf (sucf (zerof)))))) p = prfNoteq6--3,4 
u_1,0,2,3,5,4 (sucf (sucf (sucf (sucf (sucf (zerof)))))) (sucf (sucf (sucf (zerof)))) p = ncom prfNoteq6--3,4 

u_1,0,2,3,5,4 (sucf (sucf (sucf (sucf (zerof))))) (sucf (sucf (sucf (sucf (sucf (zerof)))))) p = ncom prfNoteq6--4,5 
u_1,0,2,3,5,4 (sucf (sucf (sucf (sucf (sucf (zerof)))))) (sucf (sucf (sucf (sucf (zerof))))) p = prfNoteq6--4,5 

u_1,0,3,2,5,4 : (i j : Fin 6) → (i ≢ j) → nth p_1,0,3,2,5,4 i ≢ nth p_1,0,3,2,5,4 j 
u_1,0,3,2,5,4 (zerof) (zerof) p = ⊥-elim (p refl)
u_1,0,3,2,5,4 (sucf (zerof)) (sucf (zerof)) p = ⊥-elim (p refl)
u_1,0,3,2,5,4 (sucf (sucf (zerof))) (sucf (sucf (zerof))) p = ⊥-elim (p refl)
u_1,0,3,2,5,4 (sucf (sucf (sucf (zerof)))) (sucf (sucf (sucf (zerof)))) p = ⊥-elim (p refl)
u_1,0,3,2,5,4 (sucf (sucf (sucf (sucf (zerof))))) (sucf (sucf (sucf (sucf (zerof))))) p = ⊥-elim (p refl)
u_1,0,3,2,5,4 (sucf (sucf (sucf (sucf (sucf (zerof)))))) (sucf (sucf (sucf (sucf (sucf (zerof)))))) p = ⊥-elim (p refl)
u_1,0,3,2,5,4 (sucf (sucf (sucf (sucf (sucf (sucf h)))))) _ = ⊥-elim (nolify h) 
u_1,0,3,2,5,4 _ (sucf (sucf (sucf (sucf (sucf (sucf h)))))) = ⊥-elim (nolify h) 

u_1,0,3,2,5,4 (zerof) (sucf (zerof)) p = ncom prfNoteq6--0,1 
u_1,0,3,2,5,4 (sucf (zerof)) (zerof) p = prfNoteq6--0,1 

u_1,0,3,2,5,4 (zerof) (sucf (sucf (zerof))) p = prfNoteq6--1,3 
u_1,0,3,2,5,4 (sucf (sucf (zerof))) (zerof) p = ncom prfNoteq6--1,3 

u_1,0,3,2,5,4 (zerof) (sucf (sucf (sucf (zerof)))) p = prfNoteq6--1,2 
u_1,0,3,2,5,4 (sucf (sucf (sucf (zerof)))) (zerof) p = ncom prfNoteq6--1,2 

u_1,0,3,2,5,4 (zerof) (sucf (sucf (sucf (sucf (zerof))))) p = prfNoteq6--1,5 
u_1,0,3,2,5,4 (sucf (sucf (sucf (sucf (zerof))))) (zerof) p = ncom prfNoteq6--1,5 

u_1,0,3,2,5,4 (zerof) (sucf (sucf (sucf (sucf (sucf (zerof)))))) p = prfNoteq6--1,4 
u_1,0,3,2,5,4 (sucf (sucf (sucf (sucf (sucf (zerof)))))) (zerof) p = ncom prfNoteq6--1,4 

u_1,0,3,2,5,4 (sucf (zerof)) (sucf (sucf (zerof))) p = prfNoteq6--0,3 
u_1,0,3,2,5,4 (sucf (sucf (zerof))) (sucf (zerof)) p = ncom prfNoteq6--0,3 

u_1,0,3,2,5,4 (sucf (zerof)) (sucf (sucf (sucf (zerof)))) p = prfNoteq6--0,2 
u_1,0,3,2,5,4 (sucf (sucf (sucf (zerof)))) (sucf (zerof)) p = ncom prfNoteq6--0,2 

u_1,0,3,2,5,4 (sucf (zerof)) (sucf (sucf (sucf (sucf (zerof))))) p = prfNoteq6--0,5 
u_1,0,3,2,5,4 (sucf (sucf (sucf (sucf (zerof))))) (sucf (zerof)) p = ncom prfNoteq6--0,5 

u_1,0,3,2,5,4 (sucf (zerof)) (sucf (sucf (sucf (sucf (sucf (zerof)))))) p = prfNoteq6--0,4 
u_1,0,3,2,5,4 (sucf (sucf (sucf (sucf (sucf (zerof)))))) (sucf (zerof)) p = ncom prfNoteq6--0,4 

u_1,0,3,2,5,4 (sucf (sucf (zerof))) (sucf (sucf (sucf (zerof)))) p = ncom prfNoteq6--2,3 
u_1,0,3,2,5,4 (sucf (sucf (sucf (zerof)))) (sucf (sucf (zerof))) p = prfNoteq6--2,3 

u_1,0,3,2,5,4 (sucf (sucf (zerof))) (sucf (sucf (sucf (sucf (zerof))))) p = prfNoteq6--3,5 
u_1,0,3,2,5,4 (sucf (sucf (sucf (sucf (zerof))))) (sucf (sucf (zerof))) p = ncom prfNoteq6--3,5 

u_1,0,3,2,5,4 (sucf (sucf (zerof))) (sucf (sucf (sucf (sucf (sucf (zerof)))))) p = prfNoteq6--3,4 
u_1,0,3,2,5,4 (sucf (sucf (sucf (sucf (sucf (zerof)))))) (sucf (sucf (zerof))) p = ncom prfNoteq6--3,4 

u_1,0,3,2,5,4 (sucf (sucf (sucf (zerof)))) (sucf (sucf (sucf (sucf (zerof))))) p = prfNoteq6--2,5 
u_1,0,3,2,5,4 (sucf (sucf (sucf (sucf (zerof))))) (sucf (sucf (sucf (zerof)))) p = ncom prfNoteq6--2,5 

u_1,0,3,2,5,4 (sucf (sucf (sucf (zerof)))) (sucf (sucf (sucf (sucf (sucf (zerof)))))) p = prfNoteq6--2,4 
u_1,0,3,2,5,4 (sucf (sucf (sucf (sucf (sucf (zerof)))))) (sucf (sucf (sucf (zerof)))) p = ncom prfNoteq6--2,4 

u_1,0,3,2,5,4 (sucf (sucf (sucf (sucf (zerof))))) (sucf (sucf (sucf (sucf (sucf (zerof)))))) p = ncom prfNoteq6--4,5 
u_1,0,3,2,5,4 (sucf (sucf (sucf (sucf (sucf (zerof)))))) (sucf (sucf (sucf (sucf (zerof))))) p = prfNoteq6--4,5 

u_1,2,0,3,5,4 : (i j : Fin 6) → (i ≢ j) → nth p_1,2,0,3,5,4 i ≢ nth p_1,2,0,3,5,4 j 
u_1,2,0,3,5,4 (zerof) (zerof) p = ⊥-elim (p refl)
u_1,2,0,3,5,4 (sucf (zerof)) (sucf (zerof)) p = ⊥-elim (p refl)
u_1,2,0,3,5,4 (sucf (sucf (zerof))) (sucf (sucf (zerof))) p = ⊥-elim (p refl)
u_1,2,0,3,5,4 (sucf (sucf (sucf (zerof)))) (sucf (sucf (sucf (zerof)))) p = ⊥-elim (p refl)
u_1,2,0,3,5,4 (sucf (sucf (sucf (sucf (zerof))))) (sucf (sucf (sucf (sucf (zerof))))) p = ⊥-elim (p refl)
u_1,2,0,3,5,4 (sucf (sucf (sucf (sucf (sucf (zerof)))))) (sucf (sucf (sucf (sucf (sucf (zerof)))))) p = ⊥-elim (p refl)
u_1,2,0,3,5,4 (sucf (sucf (sucf (sucf (sucf (sucf h)))))) _ = ⊥-elim (nolify h) 
u_1,2,0,3,5,4 _ (sucf (sucf (sucf (sucf (sucf (sucf h)))))) = ⊥-elim (nolify h) 

u_1,2,0,3,5,4 (zerof) (sucf (zerof)) p = prfNoteq6--1,2 
u_1,2,0,3,5,4 (sucf (zerof)) (zerof) p = ncom prfNoteq6--1,2 

u_1,2,0,3,5,4 (zerof) (sucf (sucf (zerof))) p = ncom prfNoteq6--0,1 
u_1,2,0,3,5,4 (sucf (sucf (zerof))) (zerof) p = prfNoteq6--0,1 

u_1,2,0,3,5,4 (zerof) (sucf (sucf (sucf (zerof)))) p = prfNoteq6--1,3 
u_1,2,0,3,5,4 (sucf (sucf (sucf (zerof)))) (zerof) p = ncom prfNoteq6--1,3 

u_1,2,0,3,5,4 (zerof) (sucf (sucf (sucf (sucf (zerof))))) p = prfNoteq6--1,5 
u_1,2,0,3,5,4 (sucf (sucf (sucf (sucf (zerof))))) (zerof) p = ncom prfNoteq6--1,5 

u_1,2,0,3,5,4 (zerof) (sucf (sucf (sucf (sucf (sucf (zerof)))))) p = prfNoteq6--1,4 
u_1,2,0,3,5,4 (sucf (sucf (sucf (sucf (sucf (zerof)))))) (zerof) p = ncom prfNoteq6--1,4 

u_1,2,0,3,5,4 (sucf (zerof)) (sucf (sucf (zerof))) p = ncom prfNoteq6--0,2 
u_1,2,0,3,5,4 (sucf (sucf (zerof))) (sucf (zerof)) p = prfNoteq6--0,2 

u_1,2,0,3,5,4 (sucf (zerof)) (sucf (sucf (sucf (zerof)))) p = prfNoteq6--2,3 
u_1,2,0,3,5,4 (sucf (sucf (sucf (zerof)))) (sucf (zerof)) p = ncom prfNoteq6--2,3 

u_1,2,0,3,5,4 (sucf (zerof)) (sucf (sucf (sucf (sucf (zerof))))) p = prfNoteq6--2,5 
u_1,2,0,3,5,4 (sucf (sucf (sucf (sucf (zerof))))) (sucf (zerof)) p = ncom prfNoteq6--2,5 

u_1,2,0,3,5,4 (sucf (zerof)) (sucf (sucf (sucf (sucf (sucf (zerof)))))) p = prfNoteq6--2,4 
u_1,2,0,3,5,4 (sucf (sucf (sucf (sucf (sucf (zerof)))))) (sucf (zerof)) p = ncom prfNoteq6--2,4 

u_1,2,0,3,5,4 (sucf (sucf (zerof))) (sucf (sucf (sucf (zerof)))) p = prfNoteq6--0,3 
u_1,2,0,3,5,4 (sucf (sucf (sucf (zerof)))) (sucf (sucf (zerof))) p = ncom prfNoteq6--0,3 

u_1,2,0,3,5,4 (sucf (sucf (zerof))) (sucf (sucf (sucf (sucf (zerof))))) p = prfNoteq6--0,5 
u_1,2,0,3,5,4 (sucf (sucf (sucf (sucf (zerof))))) (sucf (sucf (zerof))) p = ncom prfNoteq6--0,5 

u_1,2,0,3,5,4 (sucf (sucf (zerof))) (sucf (sucf (sucf (sucf (sucf (zerof)))))) p = prfNoteq6--0,4 
u_1,2,0,3,5,4 (sucf (sucf (sucf (sucf (sucf (zerof)))))) (sucf (sucf (zerof))) p = ncom prfNoteq6--0,4 

u_1,2,0,3,5,4 (sucf (sucf (sucf (zerof)))) (sucf (sucf (sucf (sucf (zerof))))) p = prfNoteq6--3,5 
u_1,2,0,3,5,4 (sucf (sucf (sucf (sucf (zerof))))) (sucf (sucf (sucf (zerof)))) p = ncom prfNoteq6--3,5 

u_1,2,0,3,5,4 (sucf (sucf (sucf (zerof)))) (sucf (sucf (sucf (sucf (sucf (zerof)))))) p = prfNoteq6--3,4 
u_1,2,0,3,5,4 (sucf (sucf (sucf (sucf (sucf (zerof)))))) (sucf (sucf (sucf (zerof)))) p = ncom prfNoteq6--3,4 

u_1,2,0,3,5,4 (sucf (sucf (sucf (sucf (zerof))))) (sucf (sucf (sucf (sucf (sucf (zerof)))))) p = ncom prfNoteq6--4,5 
u_1,2,0,3,5,4 (sucf (sucf (sucf (sucf (sucf (zerof)))))) (sucf (sucf (sucf (sucf (zerof))))) p = prfNoteq6--4,5 

u_1,2,3,0,5,4 : (i j : Fin 6) → (i ≢ j) → nth p_1,2,3,0,5,4 i ≢ nth p_1,2,3,0,5,4 j 
u_1,2,3,0,5,4 (zerof) (zerof) p = ⊥-elim (p refl)
u_1,2,3,0,5,4 (sucf (zerof)) (sucf (zerof)) p = ⊥-elim (p refl)
u_1,2,3,0,5,4 (sucf (sucf (zerof))) (sucf (sucf (zerof))) p = ⊥-elim (p refl)
u_1,2,3,0,5,4 (sucf (sucf (sucf (zerof)))) (sucf (sucf (sucf (zerof)))) p = ⊥-elim (p refl)
u_1,2,3,0,5,4 (sucf (sucf (sucf (sucf (zerof))))) (sucf (sucf (sucf (sucf (zerof))))) p = ⊥-elim (p refl)
u_1,2,3,0,5,4 (sucf (sucf (sucf (sucf (sucf (zerof)))))) (sucf (sucf (sucf (sucf (sucf (zerof)))))) p = ⊥-elim (p refl)
u_1,2,3,0,5,4 (sucf (sucf (sucf (sucf (sucf (sucf h)))))) _ = ⊥-elim (nolify h) 
u_1,2,3,0,5,4 _ (sucf (sucf (sucf (sucf (sucf (sucf h)))))) = ⊥-elim (nolify h) 

u_1,2,3,0,5,4 (zerof) (sucf (zerof)) p = prfNoteq6--1,2 
u_1,2,3,0,5,4 (sucf (zerof)) (zerof) p = ncom prfNoteq6--1,2 

u_1,2,3,0,5,4 (zerof) (sucf (sucf (zerof))) p = prfNoteq6--1,3 
u_1,2,3,0,5,4 (sucf (sucf (zerof))) (zerof) p = ncom prfNoteq6--1,3 

u_1,2,3,0,5,4 (zerof) (sucf (sucf (sucf (zerof)))) p = ncom prfNoteq6--0,1 
u_1,2,3,0,5,4 (sucf (sucf (sucf (zerof)))) (zerof) p = prfNoteq6--0,1 

u_1,2,3,0,5,4 (zerof) (sucf (sucf (sucf (sucf (zerof))))) p = prfNoteq6--1,5 
u_1,2,3,0,5,4 (sucf (sucf (sucf (sucf (zerof))))) (zerof) p = ncom prfNoteq6--1,5 

u_1,2,3,0,5,4 (zerof) (sucf (sucf (sucf (sucf (sucf (zerof)))))) p = prfNoteq6--1,4 
u_1,2,3,0,5,4 (sucf (sucf (sucf (sucf (sucf (zerof)))))) (zerof) p = ncom prfNoteq6--1,4 

u_1,2,3,0,5,4 (sucf (zerof)) (sucf (sucf (zerof))) p = prfNoteq6--2,3 
u_1,2,3,0,5,4 (sucf (sucf (zerof))) (sucf (zerof)) p = ncom prfNoteq6--2,3 

u_1,2,3,0,5,4 (sucf (zerof)) (sucf (sucf (sucf (zerof)))) p = ncom prfNoteq6--0,2 
u_1,2,3,0,5,4 (sucf (sucf (sucf (zerof)))) (sucf (zerof)) p = prfNoteq6--0,2 

u_1,2,3,0,5,4 (sucf (zerof)) (sucf (sucf (sucf (sucf (zerof))))) p = prfNoteq6--2,5 
u_1,2,3,0,5,4 (sucf (sucf (sucf (sucf (zerof))))) (sucf (zerof)) p = ncom prfNoteq6--2,5 

u_1,2,3,0,5,4 (sucf (zerof)) (sucf (sucf (sucf (sucf (sucf (zerof)))))) p = prfNoteq6--2,4 
u_1,2,3,0,5,4 (sucf (sucf (sucf (sucf (sucf (zerof)))))) (sucf (zerof)) p = ncom prfNoteq6--2,4 

u_1,2,3,0,5,4 (sucf (sucf (zerof))) (sucf (sucf (sucf (zerof)))) p = ncom prfNoteq6--0,3 
u_1,2,3,0,5,4 (sucf (sucf (sucf (zerof)))) (sucf (sucf (zerof))) p = prfNoteq6--0,3 

u_1,2,3,0,5,4 (sucf (sucf (zerof))) (sucf (sucf (sucf (sucf (zerof))))) p = prfNoteq6--3,5 
u_1,2,3,0,5,4 (sucf (sucf (sucf (sucf (zerof))))) (sucf (sucf (zerof))) p = ncom prfNoteq6--3,5 

u_1,2,3,0,5,4 (sucf (sucf (zerof))) (sucf (sucf (sucf (sucf (sucf (zerof)))))) p = prfNoteq6--3,4 
u_1,2,3,0,5,4 (sucf (sucf (sucf (sucf (sucf (zerof)))))) (sucf (sucf (zerof))) p = ncom prfNoteq6--3,4 

u_1,2,3,0,5,4 (sucf (sucf (sucf (zerof)))) (sucf (sucf (sucf (sucf (zerof))))) p = prfNoteq6--0,5 
u_1,2,3,0,5,4 (sucf (sucf (sucf (sucf (zerof))))) (sucf (sucf (sucf (zerof)))) p = ncom prfNoteq6--0,5 

u_1,2,3,0,5,4 (sucf (sucf (sucf (zerof)))) (sucf (sucf (sucf (sucf (sucf (zerof)))))) p = prfNoteq6--0,4 
u_1,2,3,0,5,4 (sucf (sucf (sucf (sucf (sucf (zerof)))))) (sucf (sucf (sucf (zerof)))) p = ncom prfNoteq6--0,4 

u_1,2,3,0,5,4 (sucf (sucf (sucf (sucf (zerof))))) (sucf (sucf (sucf (sucf (sucf (zerof)))))) p = ncom prfNoteq6--4,5 
u_1,2,3,0,5,4 (sucf (sucf (sucf (sucf (sucf (zerof)))))) (sucf (sucf (sucf (sucf (zerof))))) p = prfNoteq6--4,5 

u_1,3,0,2,5,4 : (i j : Fin 6) → (i ≢ j) → nth p_1,3,0,2,5,4 i ≢ nth p_1,3,0,2,5,4 j 
u_1,3,0,2,5,4 (zerof) (zerof) p = ⊥-elim (p refl)
u_1,3,0,2,5,4 (sucf (zerof)) (sucf (zerof)) p = ⊥-elim (p refl)
u_1,3,0,2,5,4 (sucf (sucf (zerof))) (sucf (sucf (zerof))) p = ⊥-elim (p refl)
u_1,3,0,2,5,4 (sucf (sucf (sucf (zerof)))) (sucf (sucf (sucf (zerof)))) p = ⊥-elim (p refl)
u_1,3,0,2,5,4 (sucf (sucf (sucf (sucf (zerof))))) (sucf (sucf (sucf (sucf (zerof))))) p = ⊥-elim (p refl)
u_1,3,0,2,5,4 (sucf (sucf (sucf (sucf (sucf (zerof)))))) (sucf (sucf (sucf (sucf (sucf (zerof)))))) p = ⊥-elim (p refl)
u_1,3,0,2,5,4 (sucf (sucf (sucf (sucf (sucf (sucf h)))))) _ = ⊥-elim (nolify h) 
u_1,3,0,2,5,4 _ (sucf (sucf (sucf (sucf (sucf (sucf h)))))) = ⊥-elim (nolify h) 

u_1,3,0,2,5,4 (zerof) (sucf (zerof)) p = prfNoteq6--1,3 
u_1,3,0,2,5,4 (sucf (zerof)) (zerof) p = ncom prfNoteq6--1,3 

u_1,3,0,2,5,4 (zerof) (sucf (sucf (zerof))) p = ncom prfNoteq6--0,1 
u_1,3,0,2,5,4 (sucf (sucf (zerof))) (zerof) p = prfNoteq6--0,1 

u_1,3,0,2,5,4 (zerof) (sucf (sucf (sucf (zerof)))) p = prfNoteq6--1,2 
u_1,3,0,2,5,4 (sucf (sucf (sucf (zerof)))) (zerof) p = ncom prfNoteq6--1,2 

u_1,3,0,2,5,4 (zerof) (sucf (sucf (sucf (sucf (zerof))))) p = prfNoteq6--1,5 
u_1,3,0,2,5,4 (sucf (sucf (sucf (sucf (zerof))))) (zerof) p = ncom prfNoteq6--1,5 

u_1,3,0,2,5,4 (zerof) (sucf (sucf (sucf (sucf (sucf (zerof)))))) p = prfNoteq6--1,4 
u_1,3,0,2,5,4 (sucf (sucf (sucf (sucf (sucf (zerof)))))) (zerof) p = ncom prfNoteq6--1,4 

u_1,3,0,2,5,4 (sucf (zerof)) (sucf (sucf (zerof))) p = ncom prfNoteq6--0,3 
u_1,3,0,2,5,4 (sucf (sucf (zerof))) (sucf (zerof)) p = prfNoteq6--0,3 

u_1,3,0,2,5,4 (sucf (zerof)) (sucf (sucf (sucf (zerof)))) p = ncom prfNoteq6--2,3 
u_1,3,0,2,5,4 (sucf (sucf (sucf (zerof)))) (sucf (zerof)) p = prfNoteq6--2,3 

u_1,3,0,2,5,4 (sucf (zerof)) (sucf (sucf (sucf (sucf (zerof))))) p = prfNoteq6--3,5 
u_1,3,0,2,5,4 (sucf (sucf (sucf (sucf (zerof))))) (sucf (zerof)) p = ncom prfNoteq6--3,5 

u_1,3,0,2,5,4 (sucf (zerof)) (sucf (sucf (sucf (sucf (sucf (zerof)))))) p = prfNoteq6--3,4 
u_1,3,0,2,5,4 (sucf (sucf (sucf (sucf (sucf (zerof)))))) (sucf (zerof)) p = ncom prfNoteq6--3,4 

u_1,3,0,2,5,4 (sucf (sucf (zerof))) (sucf (sucf (sucf (zerof)))) p = prfNoteq6--0,2 
u_1,3,0,2,5,4 (sucf (sucf (sucf (zerof)))) (sucf (sucf (zerof))) p = ncom prfNoteq6--0,2 

u_1,3,0,2,5,4 (sucf (sucf (zerof))) (sucf (sucf (sucf (sucf (zerof))))) p = prfNoteq6--0,5 
u_1,3,0,2,5,4 (sucf (sucf (sucf (sucf (zerof))))) (sucf (sucf (zerof))) p = ncom prfNoteq6--0,5 

u_1,3,0,2,5,4 (sucf (sucf (zerof))) (sucf (sucf (sucf (sucf (sucf (zerof)))))) p = prfNoteq6--0,4 
u_1,3,0,2,5,4 (sucf (sucf (sucf (sucf (sucf (zerof)))))) (sucf (sucf (zerof))) p = ncom prfNoteq6--0,4 

u_1,3,0,2,5,4 (sucf (sucf (sucf (zerof)))) (sucf (sucf (sucf (sucf (zerof))))) p = prfNoteq6--2,5 
u_1,3,0,2,5,4 (sucf (sucf (sucf (sucf (zerof))))) (sucf (sucf (sucf (zerof)))) p = ncom prfNoteq6--2,5 

u_1,3,0,2,5,4 (sucf (sucf (sucf (zerof)))) (sucf (sucf (sucf (sucf (sucf (zerof)))))) p = prfNoteq6--2,4 
u_1,3,0,2,5,4 (sucf (sucf (sucf (sucf (sucf (zerof)))))) (sucf (sucf (sucf (zerof)))) p = ncom prfNoteq6--2,4 

u_1,3,0,2,5,4 (sucf (sucf (sucf (sucf (zerof))))) (sucf (sucf (sucf (sucf (sucf (zerof)))))) p = ncom prfNoteq6--4,5 
u_1,3,0,2,5,4 (sucf (sucf (sucf (sucf (sucf (zerof)))))) (sucf (sucf (sucf (sucf (zerof))))) p = prfNoteq6--4,5 

u_2,0,1,3,5,4 : (i j : Fin 6) → (i ≢ j) → nth p_2,0,1,3,5,4 i ≢ nth p_2,0,1,3,5,4 j 
u_2,0,1,3,5,4 (zerof) (zerof) p = ⊥-elim (p refl)
u_2,0,1,3,5,4 (sucf (zerof)) (sucf (zerof)) p = ⊥-elim (p refl)
u_2,0,1,3,5,4 (sucf (sucf (zerof))) (sucf (sucf (zerof))) p = ⊥-elim (p refl)
u_2,0,1,3,5,4 (sucf (sucf (sucf (zerof)))) (sucf (sucf (sucf (zerof)))) p = ⊥-elim (p refl)
u_2,0,1,3,5,4 (sucf (sucf (sucf (sucf (zerof))))) (sucf (sucf (sucf (sucf (zerof))))) p = ⊥-elim (p refl)
u_2,0,1,3,5,4 (sucf (sucf (sucf (sucf (sucf (zerof)))))) (sucf (sucf (sucf (sucf (sucf (zerof)))))) p = ⊥-elim (p refl)
u_2,0,1,3,5,4 (sucf (sucf (sucf (sucf (sucf (sucf h)))))) _ = ⊥-elim (nolify h) 
u_2,0,1,3,5,4 _ (sucf (sucf (sucf (sucf (sucf (sucf h)))))) = ⊥-elim (nolify h) 

u_2,0,1,3,5,4 (zerof) (sucf (zerof)) p = ncom prfNoteq6--0,2 
u_2,0,1,3,5,4 (sucf (zerof)) (zerof) p = prfNoteq6--0,2 

u_2,0,1,3,5,4 (zerof) (sucf (sucf (zerof))) p = ncom prfNoteq6--1,2 
u_2,0,1,3,5,4 (sucf (sucf (zerof))) (zerof) p = prfNoteq6--1,2 

u_2,0,1,3,5,4 (zerof) (sucf (sucf (sucf (zerof)))) p = prfNoteq6--2,3 
u_2,0,1,3,5,4 (sucf (sucf (sucf (zerof)))) (zerof) p = ncom prfNoteq6--2,3 

u_2,0,1,3,5,4 (zerof) (sucf (sucf (sucf (sucf (zerof))))) p = prfNoteq6--2,5 
u_2,0,1,3,5,4 (sucf (sucf (sucf (sucf (zerof))))) (zerof) p = ncom prfNoteq6--2,5 

u_2,0,1,3,5,4 (zerof) (sucf (sucf (sucf (sucf (sucf (zerof)))))) p = prfNoteq6--2,4 
u_2,0,1,3,5,4 (sucf (sucf (sucf (sucf (sucf (zerof)))))) (zerof) p = ncom prfNoteq6--2,4 

u_2,0,1,3,5,4 (sucf (zerof)) (sucf (sucf (zerof))) p = prfNoteq6--0,1 
u_2,0,1,3,5,4 (sucf (sucf (zerof))) (sucf (zerof)) p = ncom prfNoteq6--0,1 

u_2,0,1,3,5,4 (sucf (zerof)) (sucf (sucf (sucf (zerof)))) p = prfNoteq6--0,3 
u_2,0,1,3,5,4 (sucf (sucf (sucf (zerof)))) (sucf (zerof)) p = ncom prfNoteq6--0,3 

u_2,0,1,3,5,4 (sucf (zerof)) (sucf (sucf (sucf (sucf (zerof))))) p = prfNoteq6--0,5 
u_2,0,1,3,5,4 (sucf (sucf (sucf (sucf (zerof))))) (sucf (zerof)) p = ncom prfNoteq6--0,5 

u_2,0,1,3,5,4 (sucf (zerof)) (sucf (sucf (sucf (sucf (sucf (zerof)))))) p = prfNoteq6--0,4 
u_2,0,1,3,5,4 (sucf (sucf (sucf (sucf (sucf (zerof)))))) (sucf (zerof)) p = ncom prfNoteq6--0,4 

u_2,0,1,3,5,4 (sucf (sucf (zerof))) (sucf (sucf (sucf (zerof)))) p = prfNoteq6--1,3 
u_2,0,1,3,5,4 (sucf (sucf (sucf (zerof)))) (sucf (sucf (zerof))) p = ncom prfNoteq6--1,3 

u_2,0,1,3,5,4 (sucf (sucf (zerof))) (sucf (sucf (sucf (sucf (zerof))))) p = prfNoteq6--1,5 
u_2,0,1,3,5,4 (sucf (sucf (sucf (sucf (zerof))))) (sucf (sucf (zerof))) p = ncom prfNoteq6--1,5 

u_2,0,1,3,5,4 (sucf (sucf (zerof))) (sucf (sucf (sucf (sucf (sucf (zerof)))))) p = prfNoteq6--1,4 
u_2,0,1,3,5,4 (sucf (sucf (sucf (sucf (sucf (zerof)))))) (sucf (sucf (zerof))) p = ncom prfNoteq6--1,4 

u_2,0,1,3,5,4 (sucf (sucf (sucf (zerof)))) (sucf (sucf (sucf (sucf (zerof))))) p = prfNoteq6--3,5 
u_2,0,1,3,5,4 (sucf (sucf (sucf (sucf (zerof))))) (sucf (sucf (sucf (zerof)))) p = ncom prfNoteq6--3,5 

u_2,0,1,3,5,4 (sucf (sucf (sucf (zerof)))) (sucf (sucf (sucf (sucf (sucf (zerof)))))) p = prfNoteq6--3,4 
u_2,0,1,3,5,4 (sucf (sucf (sucf (sucf (sucf (zerof)))))) (sucf (sucf (sucf (zerof)))) p = ncom prfNoteq6--3,4 

u_2,0,1,3,5,4 (sucf (sucf (sucf (sucf (zerof))))) (sucf (sucf (sucf (sucf (sucf (zerof)))))) p = ncom prfNoteq6--4,5 
u_2,0,1,3,5,4 (sucf (sucf (sucf (sucf (sucf (zerof)))))) (sucf (sucf (sucf (sucf (zerof))))) p = prfNoteq6--4,5 

u_2,0,3,1,5,4 : (i j : Fin 6) → (i ≢ j) → nth p_2,0,3,1,5,4 i ≢ nth p_2,0,3,1,5,4 j 
u_2,0,3,1,5,4 (zerof) (zerof) p = ⊥-elim (p refl)
u_2,0,3,1,5,4 (sucf (zerof)) (sucf (zerof)) p = ⊥-elim (p refl)
u_2,0,3,1,5,4 (sucf (sucf (zerof))) (sucf (sucf (zerof))) p = ⊥-elim (p refl)
u_2,0,3,1,5,4 (sucf (sucf (sucf (zerof)))) (sucf (sucf (sucf (zerof)))) p = ⊥-elim (p refl)
u_2,0,3,1,5,4 (sucf (sucf (sucf (sucf (zerof))))) (sucf (sucf (sucf (sucf (zerof))))) p = ⊥-elim (p refl)
u_2,0,3,1,5,4 (sucf (sucf (sucf (sucf (sucf (zerof)))))) (sucf (sucf (sucf (sucf (sucf (zerof)))))) p = ⊥-elim (p refl)
u_2,0,3,1,5,4 (sucf (sucf (sucf (sucf (sucf (sucf h)))))) _ = ⊥-elim (nolify h) 
u_2,0,3,1,5,4 _ (sucf (sucf (sucf (sucf (sucf (sucf h)))))) = ⊥-elim (nolify h) 

u_2,0,3,1,5,4 (zerof) (sucf (zerof)) p = ncom prfNoteq6--0,2 
u_2,0,3,1,5,4 (sucf (zerof)) (zerof) p = prfNoteq6--0,2 

u_2,0,3,1,5,4 (zerof) (sucf (sucf (zerof))) p = prfNoteq6--2,3 
u_2,0,3,1,5,4 (sucf (sucf (zerof))) (zerof) p = ncom prfNoteq6--2,3 

u_2,0,3,1,5,4 (zerof) (sucf (sucf (sucf (zerof)))) p = ncom prfNoteq6--1,2 
u_2,0,3,1,5,4 (sucf (sucf (sucf (zerof)))) (zerof) p = prfNoteq6--1,2 

u_2,0,3,1,5,4 (zerof) (sucf (sucf (sucf (sucf (zerof))))) p = prfNoteq6--2,5 
u_2,0,3,1,5,4 (sucf (sucf (sucf (sucf (zerof))))) (zerof) p = ncom prfNoteq6--2,5 

u_2,0,3,1,5,4 (zerof) (sucf (sucf (sucf (sucf (sucf (zerof)))))) p = prfNoteq6--2,4 
u_2,0,3,1,5,4 (sucf (sucf (sucf (sucf (sucf (zerof)))))) (zerof) p = ncom prfNoteq6--2,4 

u_2,0,3,1,5,4 (sucf (zerof)) (sucf (sucf (zerof))) p = prfNoteq6--0,3 
u_2,0,3,1,5,4 (sucf (sucf (zerof))) (sucf (zerof)) p = ncom prfNoteq6--0,3 

u_2,0,3,1,5,4 (sucf (zerof)) (sucf (sucf (sucf (zerof)))) p = prfNoteq6--0,1 
u_2,0,3,1,5,4 (sucf (sucf (sucf (zerof)))) (sucf (zerof)) p = ncom prfNoteq6--0,1 

u_2,0,3,1,5,4 (sucf (zerof)) (sucf (sucf (sucf (sucf (zerof))))) p = prfNoteq6--0,5 
u_2,0,3,1,5,4 (sucf (sucf (sucf (sucf (zerof))))) (sucf (zerof)) p = ncom prfNoteq6--0,5 

u_2,0,3,1,5,4 (sucf (zerof)) (sucf (sucf (sucf (sucf (sucf (zerof)))))) p = prfNoteq6--0,4 
u_2,0,3,1,5,4 (sucf (sucf (sucf (sucf (sucf (zerof)))))) (sucf (zerof)) p = ncom prfNoteq6--0,4 

u_2,0,3,1,5,4 (sucf (sucf (zerof))) (sucf (sucf (sucf (zerof)))) p = ncom prfNoteq6--1,3 
u_2,0,3,1,5,4 (sucf (sucf (sucf (zerof)))) (sucf (sucf (zerof))) p = prfNoteq6--1,3 

u_2,0,3,1,5,4 (sucf (sucf (zerof))) (sucf (sucf (sucf (sucf (zerof))))) p = prfNoteq6--3,5 
u_2,0,3,1,5,4 (sucf (sucf (sucf (sucf (zerof))))) (sucf (sucf (zerof))) p = ncom prfNoteq6--3,5 

u_2,0,3,1,5,4 (sucf (sucf (zerof))) (sucf (sucf (sucf (sucf (sucf (zerof)))))) p = prfNoteq6--3,4 
u_2,0,3,1,5,4 (sucf (sucf (sucf (sucf (sucf (zerof)))))) (sucf (sucf (zerof))) p = ncom prfNoteq6--3,4 

u_2,0,3,1,5,4 (sucf (sucf (sucf (zerof)))) (sucf (sucf (sucf (sucf (zerof))))) p = prfNoteq6--1,5 
u_2,0,3,1,5,4 (sucf (sucf (sucf (sucf (zerof))))) (sucf (sucf (sucf (zerof)))) p = ncom prfNoteq6--1,5 

u_2,0,3,1,5,4 (sucf (sucf (sucf (zerof)))) (sucf (sucf (sucf (sucf (sucf (zerof)))))) p = prfNoteq6--1,4 
u_2,0,3,1,5,4 (sucf (sucf (sucf (sucf (sucf (zerof)))))) (sucf (sucf (sucf (zerof)))) p = ncom prfNoteq6--1,4 

u_2,0,3,1,5,4 (sucf (sucf (sucf (sucf (zerof))))) (sucf (sucf (sucf (sucf (sucf (zerof)))))) p = ncom prfNoteq6--4,5 
u_2,0,3,1,5,4 (sucf (sucf (sucf (sucf (sucf (zerof)))))) (sucf (sucf (sucf (sucf (zerof))))) p = prfNoteq6--4,5 

u_2,3,0,1,5,4 : (i j : Fin 6) → (i ≢ j) → nth p_2,3,0,1,5,4 i ≢ nth p_2,3,0,1,5,4 j 
u_2,3,0,1,5,4 (zerof) (zerof) p = ⊥-elim (p refl)
u_2,3,0,1,5,4 (sucf (zerof)) (sucf (zerof)) p = ⊥-elim (p refl)
u_2,3,0,1,5,4 (sucf (sucf (zerof))) (sucf (sucf (zerof))) p = ⊥-elim (p refl)
u_2,3,0,1,5,4 (sucf (sucf (sucf (zerof)))) (sucf (sucf (sucf (zerof)))) p = ⊥-elim (p refl)
u_2,3,0,1,5,4 (sucf (sucf (sucf (sucf (zerof))))) (sucf (sucf (sucf (sucf (zerof))))) p = ⊥-elim (p refl)
u_2,3,0,1,5,4 (sucf (sucf (sucf (sucf (sucf (zerof)))))) (sucf (sucf (sucf (sucf (sucf (zerof)))))) p = ⊥-elim (p refl)
u_2,3,0,1,5,4 (sucf (sucf (sucf (sucf (sucf (sucf h)))))) _ = ⊥-elim (nolify h) 
u_2,3,0,1,5,4 _ (sucf (sucf (sucf (sucf (sucf (sucf h)))))) = ⊥-elim (nolify h) 

u_2,3,0,1,5,4 (zerof) (sucf (zerof)) p = prfNoteq6--2,3 
u_2,3,0,1,5,4 (sucf (zerof)) (zerof) p = ncom prfNoteq6--2,3 

u_2,3,0,1,5,4 (zerof) (sucf (sucf (zerof))) p = ncom prfNoteq6--0,2 
u_2,3,0,1,5,4 (sucf (sucf (zerof))) (zerof) p = prfNoteq6--0,2 

u_2,3,0,1,5,4 (zerof) (sucf (sucf (sucf (zerof)))) p = ncom prfNoteq6--1,2 
u_2,3,0,1,5,4 (sucf (sucf (sucf (zerof)))) (zerof) p = prfNoteq6--1,2 

u_2,3,0,1,5,4 (zerof) (sucf (sucf (sucf (sucf (zerof))))) p = prfNoteq6--2,5 
u_2,3,0,1,5,4 (sucf (sucf (sucf (sucf (zerof))))) (zerof) p = ncom prfNoteq6--2,5 

u_2,3,0,1,5,4 (zerof) (sucf (sucf (sucf (sucf (sucf (zerof)))))) p = prfNoteq6--2,4 
u_2,3,0,1,5,4 (sucf (sucf (sucf (sucf (sucf (zerof)))))) (zerof) p = ncom prfNoteq6--2,4 

u_2,3,0,1,5,4 (sucf (zerof)) (sucf (sucf (zerof))) p = ncom prfNoteq6--0,3 
u_2,3,0,1,5,4 (sucf (sucf (zerof))) (sucf (zerof)) p = prfNoteq6--0,3 

u_2,3,0,1,5,4 (sucf (zerof)) (sucf (sucf (sucf (zerof)))) p = ncom prfNoteq6--1,3 
u_2,3,0,1,5,4 (sucf (sucf (sucf (zerof)))) (sucf (zerof)) p = prfNoteq6--1,3 

u_2,3,0,1,5,4 (sucf (zerof)) (sucf (sucf (sucf (sucf (zerof))))) p = prfNoteq6--3,5 
u_2,3,0,1,5,4 (sucf (sucf (sucf (sucf (zerof))))) (sucf (zerof)) p = ncom prfNoteq6--3,5 

u_2,3,0,1,5,4 (sucf (zerof)) (sucf (sucf (sucf (sucf (sucf (zerof)))))) p = prfNoteq6--3,4 
u_2,3,0,1,5,4 (sucf (sucf (sucf (sucf (sucf (zerof)))))) (sucf (zerof)) p = ncom prfNoteq6--3,4 

u_2,3,0,1,5,4 (sucf (sucf (zerof))) (sucf (sucf (sucf (zerof)))) p = prfNoteq6--0,1 
u_2,3,0,1,5,4 (sucf (sucf (sucf (zerof)))) (sucf (sucf (zerof))) p = ncom prfNoteq6--0,1 

u_2,3,0,1,5,4 (sucf (sucf (zerof))) (sucf (sucf (sucf (sucf (zerof))))) p = prfNoteq6--0,5 
u_2,3,0,1,5,4 (sucf (sucf (sucf (sucf (zerof))))) (sucf (sucf (zerof))) p = ncom prfNoteq6--0,5 

u_2,3,0,1,5,4 (sucf (sucf (zerof))) (sucf (sucf (sucf (sucf (sucf (zerof)))))) p = prfNoteq6--0,4 
u_2,3,0,1,5,4 (sucf (sucf (sucf (sucf (sucf (zerof)))))) (sucf (sucf (zerof))) p = ncom prfNoteq6--0,4 

u_2,3,0,1,5,4 (sucf (sucf (sucf (zerof)))) (sucf (sucf (sucf (sucf (zerof))))) p = prfNoteq6--1,5 
u_2,3,0,1,5,4 (sucf (sucf (sucf (sucf (zerof))))) (sucf (sucf (sucf (zerof)))) p = ncom prfNoteq6--1,5 

u_2,3,0,1,5,4 (sucf (sucf (sucf (zerof)))) (sucf (sucf (sucf (sucf (sucf (zerof)))))) p = prfNoteq6--1,4 
u_2,3,0,1,5,4 (sucf (sucf (sucf (sucf (sucf (zerof)))))) (sucf (sucf (sucf (zerof)))) p = ncom prfNoteq6--1,4 

u_2,3,0,1,5,4 (sucf (sucf (sucf (sucf (zerof))))) (sucf (sucf (sucf (sucf (sucf (zerof)))))) p = ncom prfNoteq6--4,5 
u_2,3,0,1,5,4 (sucf (sucf (sucf (sucf (sucf (zerof)))))) (sucf (sucf (sucf (sucf (zerof))))) p = prfNoteq6--4,5 

u_3,0,1,2,5,4 : (i j : Fin 6) → (i ≢ j) → nth p_3,0,1,2,5,4 i ≢ nth p_3,0,1,2,5,4 j 
u_3,0,1,2,5,4 (zerof) (zerof) p = ⊥-elim (p refl)
u_3,0,1,2,5,4 (sucf (zerof)) (sucf (zerof)) p = ⊥-elim (p refl)
u_3,0,1,2,5,4 (sucf (sucf (zerof))) (sucf (sucf (zerof))) p = ⊥-elim (p refl)
u_3,0,1,2,5,4 (sucf (sucf (sucf (zerof)))) (sucf (sucf (sucf (zerof)))) p = ⊥-elim (p refl)
u_3,0,1,2,5,4 (sucf (sucf (sucf (sucf (zerof))))) (sucf (sucf (sucf (sucf (zerof))))) p = ⊥-elim (p refl)
u_3,0,1,2,5,4 (sucf (sucf (sucf (sucf (sucf (zerof)))))) (sucf (sucf (sucf (sucf (sucf (zerof)))))) p = ⊥-elim (p refl)
u_3,0,1,2,5,4 (sucf (sucf (sucf (sucf (sucf (sucf h)))))) _ = ⊥-elim (nolify h) 
u_3,0,1,2,5,4 _ (sucf (sucf (sucf (sucf (sucf (sucf h)))))) = ⊥-elim (nolify h) 

u_3,0,1,2,5,4 (zerof) (sucf (zerof)) p = ncom prfNoteq6--0,3 
u_3,0,1,2,5,4 (sucf (zerof)) (zerof) p = prfNoteq6--0,3 

u_3,0,1,2,5,4 (zerof) (sucf (sucf (zerof))) p = ncom prfNoteq6--1,3 
u_3,0,1,2,5,4 (sucf (sucf (zerof))) (zerof) p = prfNoteq6--1,3 

u_3,0,1,2,5,4 (zerof) (sucf (sucf (sucf (zerof)))) p = ncom prfNoteq6--2,3 
u_3,0,1,2,5,4 (sucf (sucf (sucf (zerof)))) (zerof) p = prfNoteq6--2,3 

u_3,0,1,2,5,4 (zerof) (sucf (sucf (sucf (sucf (zerof))))) p = prfNoteq6--3,5 
u_3,0,1,2,5,4 (sucf (sucf (sucf (sucf (zerof))))) (zerof) p = ncom prfNoteq6--3,5 

u_3,0,1,2,5,4 (zerof) (sucf (sucf (sucf (sucf (sucf (zerof)))))) p = prfNoteq6--3,4 
u_3,0,1,2,5,4 (sucf (sucf (sucf (sucf (sucf (zerof)))))) (zerof) p = ncom prfNoteq6--3,4 

u_3,0,1,2,5,4 (sucf (zerof)) (sucf (sucf (zerof))) p = prfNoteq6--0,1 
u_3,0,1,2,5,4 (sucf (sucf (zerof))) (sucf (zerof)) p = ncom prfNoteq6--0,1 

u_3,0,1,2,5,4 (sucf (zerof)) (sucf (sucf (sucf (zerof)))) p = prfNoteq6--0,2 
u_3,0,1,2,5,4 (sucf (sucf (sucf (zerof)))) (sucf (zerof)) p = ncom prfNoteq6--0,2 

u_3,0,1,2,5,4 (sucf (zerof)) (sucf (sucf (sucf (sucf (zerof))))) p = prfNoteq6--0,5 
u_3,0,1,2,5,4 (sucf (sucf (sucf (sucf (zerof))))) (sucf (zerof)) p = ncom prfNoteq6--0,5 

u_3,0,1,2,5,4 (sucf (zerof)) (sucf (sucf (sucf (sucf (sucf (zerof)))))) p = prfNoteq6--0,4 
u_3,0,1,2,5,4 (sucf (sucf (sucf (sucf (sucf (zerof)))))) (sucf (zerof)) p = ncom prfNoteq6--0,4 

u_3,0,1,2,5,4 (sucf (sucf (zerof))) (sucf (sucf (sucf (zerof)))) p = prfNoteq6--1,2 
u_3,0,1,2,5,4 (sucf (sucf (sucf (zerof)))) (sucf (sucf (zerof))) p = ncom prfNoteq6--1,2 

u_3,0,1,2,5,4 (sucf (sucf (zerof))) (sucf (sucf (sucf (sucf (zerof))))) p = prfNoteq6--1,5 
u_3,0,1,2,5,4 (sucf (sucf (sucf (sucf (zerof))))) (sucf (sucf (zerof))) p = ncom prfNoteq6--1,5 

u_3,0,1,2,5,4 (sucf (sucf (zerof))) (sucf (sucf (sucf (sucf (sucf (zerof)))))) p = prfNoteq6--1,4 
u_3,0,1,2,5,4 (sucf (sucf (sucf (sucf (sucf (zerof)))))) (sucf (sucf (zerof))) p = ncom prfNoteq6--1,4 

u_3,0,1,2,5,4 (sucf (sucf (sucf (zerof)))) (sucf (sucf (sucf (sucf (zerof))))) p = prfNoteq6--2,5 
u_3,0,1,2,5,4 (sucf (sucf (sucf (sucf (zerof))))) (sucf (sucf (sucf (zerof)))) p = ncom prfNoteq6--2,5 

u_3,0,1,2,5,4 (sucf (sucf (sucf (zerof)))) (sucf (sucf (sucf (sucf (sucf (zerof)))))) p = prfNoteq6--2,4 
u_3,0,1,2,5,4 (sucf (sucf (sucf (sucf (sucf (zerof)))))) (sucf (sucf (sucf (zerof)))) p = ncom prfNoteq6--2,4 

u_3,0,1,2,5,4 (sucf (sucf (sucf (sucf (zerof))))) (sucf (sucf (sucf (sucf (sucf (zerof)))))) p = ncom prfNoteq6--4,5 
u_3,0,1,2,5,4 (sucf (sucf (sucf (sucf (sucf (zerof)))))) (sucf (sucf (sucf (sucf (zerof))))) p = prfNoteq6--4,5 

u_3,0,2,1,5,4 : (i j : Fin 6) → (i ≢ j) → nth p_3,0,2,1,5,4 i ≢ nth p_3,0,2,1,5,4 j 
u_3,0,2,1,5,4 (zerof) (zerof) p = ⊥-elim (p refl)
u_3,0,2,1,5,4 (sucf (zerof)) (sucf (zerof)) p = ⊥-elim (p refl)
u_3,0,2,1,5,4 (sucf (sucf (zerof))) (sucf (sucf (zerof))) p = ⊥-elim (p refl)
u_3,0,2,1,5,4 (sucf (sucf (sucf (zerof)))) (sucf (sucf (sucf (zerof)))) p = ⊥-elim (p refl)
u_3,0,2,1,5,4 (sucf (sucf (sucf (sucf (zerof))))) (sucf (sucf (sucf (sucf (zerof))))) p = ⊥-elim (p refl)
u_3,0,2,1,5,4 (sucf (sucf (sucf (sucf (sucf (zerof)))))) (sucf (sucf (sucf (sucf (sucf (zerof)))))) p = ⊥-elim (p refl)
u_3,0,2,1,5,4 (sucf (sucf (sucf (sucf (sucf (sucf h)))))) _ = ⊥-elim (nolify h) 
u_3,0,2,1,5,4 _ (sucf (sucf (sucf (sucf (sucf (sucf h)))))) = ⊥-elim (nolify h) 

u_3,0,2,1,5,4 (zerof) (sucf (zerof)) p = ncom prfNoteq6--0,3 
u_3,0,2,1,5,4 (sucf (zerof)) (zerof) p = prfNoteq6--0,3 

u_3,0,2,1,5,4 (zerof) (sucf (sucf (zerof))) p = ncom prfNoteq6--2,3 
u_3,0,2,1,5,4 (sucf (sucf (zerof))) (zerof) p = prfNoteq6--2,3 

u_3,0,2,1,5,4 (zerof) (sucf (sucf (sucf (zerof)))) p = ncom prfNoteq6--1,3 
u_3,0,2,1,5,4 (sucf (sucf (sucf (zerof)))) (zerof) p = prfNoteq6--1,3 

u_3,0,2,1,5,4 (zerof) (sucf (sucf (sucf (sucf (zerof))))) p = prfNoteq6--3,5 
u_3,0,2,1,5,4 (sucf (sucf (sucf (sucf (zerof))))) (zerof) p = ncom prfNoteq6--3,5 

u_3,0,2,1,5,4 (zerof) (sucf (sucf (sucf (sucf (sucf (zerof)))))) p = prfNoteq6--3,4 
u_3,0,2,1,5,4 (sucf (sucf (sucf (sucf (sucf (zerof)))))) (zerof) p = ncom prfNoteq6--3,4 

u_3,0,2,1,5,4 (sucf (zerof)) (sucf (sucf (zerof))) p = prfNoteq6--0,2 
u_3,0,2,1,5,4 (sucf (sucf (zerof))) (sucf (zerof)) p = ncom prfNoteq6--0,2 

u_3,0,2,1,5,4 (sucf (zerof)) (sucf (sucf (sucf (zerof)))) p = prfNoteq6--0,1 
u_3,0,2,1,5,4 (sucf (sucf (sucf (zerof)))) (sucf (zerof)) p = ncom prfNoteq6--0,1 

u_3,0,2,1,5,4 (sucf (zerof)) (sucf (sucf (sucf (sucf (zerof))))) p = prfNoteq6--0,5 
u_3,0,2,1,5,4 (sucf (sucf (sucf (sucf (zerof))))) (sucf (zerof)) p = ncom prfNoteq6--0,5 

u_3,0,2,1,5,4 (sucf (zerof)) (sucf (sucf (sucf (sucf (sucf (zerof)))))) p = prfNoteq6--0,4 
u_3,0,2,1,5,4 (sucf (sucf (sucf (sucf (sucf (zerof)))))) (sucf (zerof)) p = ncom prfNoteq6--0,4 

u_3,0,2,1,5,4 (sucf (sucf (zerof))) (sucf (sucf (sucf (zerof)))) p = ncom prfNoteq6--1,2 
u_3,0,2,1,5,4 (sucf (sucf (sucf (zerof)))) (sucf (sucf (zerof))) p = prfNoteq6--1,2 

u_3,0,2,1,5,4 (sucf (sucf (zerof))) (sucf (sucf (sucf (sucf (zerof))))) p = prfNoteq6--2,5 
u_3,0,2,1,5,4 (sucf (sucf (sucf (sucf (zerof))))) (sucf (sucf (zerof))) p = ncom prfNoteq6--2,5 

u_3,0,2,1,5,4 (sucf (sucf (zerof))) (sucf (sucf (sucf (sucf (sucf (zerof)))))) p = prfNoteq6--2,4 
u_3,0,2,1,5,4 (sucf (sucf (sucf (sucf (sucf (zerof)))))) (sucf (sucf (zerof))) p = ncom prfNoteq6--2,4 

u_3,0,2,1,5,4 (sucf (sucf (sucf (zerof)))) (sucf (sucf (sucf (sucf (zerof))))) p = prfNoteq6--1,5 
u_3,0,2,1,5,4 (sucf (sucf (sucf (sucf (zerof))))) (sucf (sucf (sucf (zerof)))) p = ncom prfNoteq6--1,5 

u_3,0,2,1,5,4 (sucf (sucf (sucf (zerof)))) (sucf (sucf (sucf (sucf (sucf (zerof)))))) p = prfNoteq6--1,4 
u_3,0,2,1,5,4 (sucf (sucf (sucf (sucf (sucf (zerof)))))) (sucf (sucf (sucf (zerof)))) p = ncom prfNoteq6--1,4 

u_3,0,2,1,5,4 (sucf (sucf (sucf (sucf (zerof))))) (sucf (sucf (sucf (sucf (sucf (zerof)))))) p = ncom prfNoteq6--4,5 
u_3,0,2,1,5,4 (sucf (sucf (sucf (sucf (sucf (zerof)))))) (sucf (sucf (sucf (sucf (zerof))))) p = prfNoteq6--4,5 

u_3,1,0,2,5,4 : (i j : Fin 6) → (i ≢ j) → nth p_3,1,0,2,5,4 i ≢ nth p_3,1,0,2,5,4 j 
u_3,1,0,2,5,4 (zerof) (zerof) p = ⊥-elim (p refl)
u_3,1,0,2,5,4 (sucf (zerof)) (sucf (zerof)) p = ⊥-elim (p refl)
u_3,1,0,2,5,4 (sucf (sucf (zerof))) (sucf (sucf (zerof))) p = ⊥-elim (p refl)
u_3,1,0,2,5,4 (sucf (sucf (sucf (zerof)))) (sucf (sucf (sucf (zerof)))) p = ⊥-elim (p refl)
u_3,1,0,2,5,4 (sucf (sucf (sucf (sucf (zerof))))) (sucf (sucf (sucf (sucf (zerof))))) p = ⊥-elim (p refl)
u_3,1,0,2,5,4 (sucf (sucf (sucf (sucf (sucf (zerof)))))) (sucf (sucf (sucf (sucf (sucf (zerof)))))) p = ⊥-elim (p refl)
u_3,1,0,2,5,4 (sucf (sucf (sucf (sucf (sucf (sucf h)))))) _ = ⊥-elim (nolify h) 
u_3,1,0,2,5,4 _ (sucf (sucf (sucf (sucf (sucf (sucf h)))))) = ⊥-elim (nolify h) 

u_3,1,0,2,5,4 (zerof) (sucf (zerof)) p = ncom prfNoteq6--1,3 
u_3,1,0,2,5,4 (sucf (zerof)) (zerof) p = prfNoteq6--1,3 

u_3,1,0,2,5,4 (zerof) (sucf (sucf (zerof))) p = ncom prfNoteq6--0,3 
u_3,1,0,2,5,4 (sucf (sucf (zerof))) (zerof) p = prfNoteq6--0,3 

u_3,1,0,2,5,4 (zerof) (sucf (sucf (sucf (zerof)))) p = ncom prfNoteq6--2,3 
u_3,1,0,2,5,4 (sucf (sucf (sucf (zerof)))) (zerof) p = prfNoteq6--2,3 

u_3,1,0,2,5,4 (zerof) (sucf (sucf (sucf (sucf (zerof))))) p = prfNoteq6--3,5 
u_3,1,0,2,5,4 (sucf (sucf (sucf (sucf (zerof))))) (zerof) p = ncom prfNoteq6--3,5 

u_3,1,0,2,5,4 (zerof) (sucf (sucf (sucf (sucf (sucf (zerof)))))) p = prfNoteq6--3,4 
u_3,1,0,2,5,4 (sucf (sucf (sucf (sucf (sucf (zerof)))))) (zerof) p = ncom prfNoteq6--3,4 

u_3,1,0,2,5,4 (sucf (zerof)) (sucf (sucf (zerof))) p = ncom prfNoteq6--0,1 
u_3,1,0,2,5,4 (sucf (sucf (zerof))) (sucf (zerof)) p = prfNoteq6--0,1 

u_3,1,0,2,5,4 (sucf (zerof)) (sucf (sucf (sucf (zerof)))) p = prfNoteq6--1,2 
u_3,1,0,2,5,4 (sucf (sucf (sucf (zerof)))) (sucf (zerof)) p = ncom prfNoteq6--1,2 

u_3,1,0,2,5,4 (sucf (zerof)) (sucf (sucf (sucf (sucf (zerof))))) p = prfNoteq6--1,5 
u_3,1,0,2,5,4 (sucf (sucf (sucf (sucf (zerof))))) (sucf (zerof)) p = ncom prfNoteq6--1,5 

u_3,1,0,2,5,4 (sucf (zerof)) (sucf (sucf (sucf (sucf (sucf (zerof)))))) p = prfNoteq6--1,4 
u_3,1,0,2,5,4 (sucf (sucf (sucf (sucf (sucf (zerof)))))) (sucf (zerof)) p = ncom prfNoteq6--1,4 

u_3,1,0,2,5,4 (sucf (sucf (zerof))) (sucf (sucf (sucf (zerof)))) p = prfNoteq6--0,2 
u_3,1,0,2,5,4 (sucf (sucf (sucf (zerof)))) (sucf (sucf (zerof))) p = ncom prfNoteq6--0,2 

u_3,1,0,2,5,4 (sucf (sucf (zerof))) (sucf (sucf (sucf (sucf (zerof))))) p = prfNoteq6--0,5 
u_3,1,0,2,5,4 (sucf (sucf (sucf (sucf (zerof))))) (sucf (sucf (zerof))) p = ncom prfNoteq6--0,5 

u_3,1,0,2,5,4 (sucf (sucf (zerof))) (sucf (sucf (sucf (sucf (sucf (zerof)))))) p = prfNoteq6--0,4 
u_3,1,0,2,5,4 (sucf (sucf (sucf (sucf (sucf (zerof)))))) (sucf (sucf (zerof))) p = ncom prfNoteq6--0,4 

u_3,1,0,2,5,4 (sucf (sucf (sucf (zerof)))) (sucf (sucf (sucf (sucf (zerof))))) p = prfNoteq6--2,5 
u_3,1,0,2,5,4 (sucf (sucf (sucf (sucf (zerof))))) (sucf (sucf (sucf (zerof)))) p = ncom prfNoteq6--2,5 

u_3,1,0,2,5,4 (sucf (sucf (sucf (zerof)))) (sucf (sucf (sucf (sucf (sucf (zerof)))))) p = prfNoteq6--2,4 
u_3,1,0,2,5,4 (sucf (sucf (sucf (sucf (sucf (zerof)))))) (sucf (sucf (sucf (zerof)))) p = ncom prfNoteq6--2,4 

u_3,1,0,2,5,4 (sucf (sucf (sucf (sucf (zerof))))) (sucf (sucf (sucf (sucf (sucf (zerof)))))) p = ncom prfNoteq6--4,5 
u_3,1,0,2,5,4 (sucf (sucf (sucf (sucf (sucf (zerof)))))) (sucf (sucf (sucf (sucf (zerof))))) p = prfNoteq6--4,5 

u_3,1,2,0,5,4 : (i j : Fin 6) → (i ≢ j) → nth p_3,1,2,0,5,4 i ≢ nth p_3,1,2,0,5,4 j 
u_3,1,2,0,5,4 (zerof) (zerof) p = ⊥-elim (p refl)
u_3,1,2,0,5,4 (sucf (zerof)) (sucf (zerof)) p = ⊥-elim (p refl)
u_3,1,2,0,5,4 (sucf (sucf (zerof))) (sucf (sucf (zerof))) p = ⊥-elim (p refl)
u_3,1,2,0,5,4 (sucf (sucf (sucf (zerof)))) (sucf (sucf (sucf (zerof)))) p = ⊥-elim (p refl)
u_3,1,2,0,5,4 (sucf (sucf (sucf (sucf (zerof))))) (sucf (sucf (sucf (sucf (zerof))))) p = ⊥-elim (p refl)
u_3,1,2,0,5,4 (sucf (sucf (sucf (sucf (sucf (zerof)))))) (sucf (sucf (sucf (sucf (sucf (zerof)))))) p = ⊥-elim (p refl)
u_3,1,2,0,5,4 (sucf (sucf (sucf (sucf (sucf (sucf h)))))) _ = ⊥-elim (nolify h) 
u_3,1,2,0,5,4 _ (sucf (sucf (sucf (sucf (sucf (sucf h)))))) = ⊥-elim (nolify h) 

u_3,1,2,0,5,4 (zerof) (sucf (zerof)) p = ncom prfNoteq6--1,3 
u_3,1,2,0,5,4 (sucf (zerof)) (zerof) p = prfNoteq6--1,3 

u_3,1,2,0,5,4 (zerof) (sucf (sucf (zerof))) p = ncom prfNoteq6--2,3 
u_3,1,2,0,5,4 (sucf (sucf (zerof))) (zerof) p = prfNoteq6--2,3 

u_3,1,2,0,5,4 (zerof) (sucf (sucf (sucf (zerof)))) p = ncom prfNoteq6--0,3 
u_3,1,2,0,5,4 (sucf (sucf (sucf (zerof)))) (zerof) p = prfNoteq6--0,3 

u_3,1,2,0,5,4 (zerof) (sucf (sucf (sucf (sucf (zerof))))) p = prfNoteq6--3,5 
u_3,1,2,0,5,4 (sucf (sucf (sucf (sucf (zerof))))) (zerof) p = ncom prfNoteq6--3,5 

u_3,1,2,0,5,4 (zerof) (sucf (sucf (sucf (sucf (sucf (zerof)))))) p = prfNoteq6--3,4 
u_3,1,2,0,5,4 (sucf (sucf (sucf (sucf (sucf (zerof)))))) (zerof) p = ncom prfNoteq6--3,4 

u_3,1,2,0,5,4 (sucf (zerof)) (sucf (sucf (zerof))) p = prfNoteq6--1,2 
u_3,1,2,0,5,4 (sucf (sucf (zerof))) (sucf (zerof)) p = ncom prfNoteq6--1,2 

u_3,1,2,0,5,4 (sucf (zerof)) (sucf (sucf (sucf (zerof)))) p = ncom prfNoteq6--0,1 
u_3,1,2,0,5,4 (sucf (sucf (sucf (zerof)))) (sucf (zerof)) p = prfNoteq6--0,1 

u_3,1,2,0,5,4 (sucf (zerof)) (sucf (sucf (sucf (sucf (zerof))))) p = prfNoteq6--1,5 
u_3,1,2,0,5,4 (sucf (sucf (sucf (sucf (zerof))))) (sucf (zerof)) p = ncom prfNoteq6--1,5 

u_3,1,2,0,5,4 (sucf (zerof)) (sucf (sucf (sucf (sucf (sucf (zerof)))))) p = prfNoteq6--1,4 
u_3,1,2,0,5,4 (sucf (sucf (sucf (sucf (sucf (zerof)))))) (sucf (zerof)) p = ncom prfNoteq6--1,4 

u_3,1,2,0,5,4 (sucf (sucf (zerof))) (sucf (sucf (sucf (zerof)))) p = ncom prfNoteq6--0,2 
u_3,1,2,0,5,4 (sucf (sucf (sucf (zerof)))) (sucf (sucf (zerof))) p = prfNoteq6--0,2 

u_3,1,2,0,5,4 (sucf (sucf (zerof))) (sucf (sucf (sucf (sucf (zerof))))) p = prfNoteq6--2,5 
u_3,1,2,0,5,4 (sucf (sucf (sucf (sucf (zerof))))) (sucf (sucf (zerof))) p = ncom prfNoteq6--2,5 

u_3,1,2,0,5,4 (sucf (sucf (zerof))) (sucf (sucf (sucf (sucf (sucf (zerof)))))) p = prfNoteq6--2,4 
u_3,1,2,0,5,4 (sucf (sucf (sucf (sucf (sucf (zerof)))))) (sucf (sucf (zerof))) p = ncom prfNoteq6--2,4 

u_3,1,2,0,5,4 (sucf (sucf (sucf (zerof)))) (sucf (sucf (sucf (sucf (zerof))))) p = prfNoteq6--0,5 
u_3,1,2,0,5,4 (sucf (sucf (sucf (sucf (zerof))))) (sucf (sucf (sucf (zerof)))) p = ncom prfNoteq6--0,5 

u_3,1,2,0,5,4 (sucf (sucf (sucf (zerof)))) (sucf (sucf (sucf (sucf (sucf (zerof)))))) p = prfNoteq6--0,4 
u_3,1,2,0,5,4 (sucf (sucf (sucf (sucf (sucf (zerof)))))) (sucf (sucf (sucf (zerof)))) p = ncom prfNoteq6--0,4 

u_3,1,2,0,5,4 (sucf (sucf (sucf (sucf (zerof))))) (sucf (sucf (sucf (sucf (sucf (zerof)))))) p = ncom prfNoteq6--4,5 
u_3,1,2,0,5,4 (sucf (sucf (sucf (sucf (sucf (zerof)))))) (sucf (sucf (sucf (sucf (zerof))))) p = prfNoteq6--4,5 

u_3,2,0,1,5,4 : (i j : Fin 6) → (i ≢ j) → nth p_3,2,0,1,5,4 i ≢ nth p_3,2,0,1,5,4 j 
u_3,2,0,1,5,4 (zerof) (zerof) p = ⊥-elim (p refl)
u_3,2,0,1,5,4 (sucf (zerof)) (sucf (zerof)) p = ⊥-elim (p refl)
u_3,2,0,1,5,4 (sucf (sucf (zerof))) (sucf (sucf (zerof))) p = ⊥-elim (p refl)
u_3,2,0,1,5,4 (sucf (sucf (sucf (zerof)))) (sucf (sucf (sucf (zerof)))) p = ⊥-elim (p refl)
u_3,2,0,1,5,4 (sucf (sucf (sucf (sucf (zerof))))) (sucf (sucf (sucf (sucf (zerof))))) p = ⊥-elim (p refl)
u_3,2,0,1,5,4 (sucf (sucf (sucf (sucf (sucf (zerof)))))) (sucf (sucf (sucf (sucf (sucf (zerof)))))) p = ⊥-elim (p refl)
u_3,2,0,1,5,4 (sucf (sucf (sucf (sucf (sucf (sucf h)))))) _ = ⊥-elim (nolify h) 
u_3,2,0,1,5,4 _ (sucf (sucf (sucf (sucf (sucf (sucf h)))))) = ⊥-elim (nolify h) 

u_3,2,0,1,5,4 (zerof) (sucf (zerof)) p = ncom prfNoteq6--2,3 
u_3,2,0,1,5,4 (sucf (zerof)) (zerof) p = prfNoteq6--2,3 

u_3,2,0,1,5,4 (zerof) (sucf (sucf (zerof))) p = ncom prfNoteq6--0,3 
u_3,2,0,1,5,4 (sucf (sucf (zerof))) (zerof) p = prfNoteq6--0,3 

u_3,2,0,1,5,4 (zerof) (sucf (sucf (sucf (zerof)))) p = ncom prfNoteq6--1,3 
u_3,2,0,1,5,4 (sucf (sucf (sucf (zerof)))) (zerof) p = prfNoteq6--1,3 

u_3,2,0,1,5,4 (zerof) (sucf (sucf (sucf (sucf (zerof))))) p = prfNoteq6--3,5 
u_3,2,0,1,5,4 (sucf (sucf (sucf (sucf (zerof))))) (zerof) p = ncom prfNoteq6--3,5 

u_3,2,0,1,5,4 (zerof) (sucf (sucf (sucf (sucf (sucf (zerof)))))) p = prfNoteq6--3,4 
u_3,2,0,1,5,4 (sucf (sucf (sucf (sucf (sucf (zerof)))))) (zerof) p = ncom prfNoteq6--3,4 

u_3,2,0,1,5,4 (sucf (zerof)) (sucf (sucf (zerof))) p = ncom prfNoteq6--0,2 
u_3,2,0,1,5,4 (sucf (sucf (zerof))) (sucf (zerof)) p = prfNoteq6--0,2 

u_3,2,0,1,5,4 (sucf (zerof)) (sucf (sucf (sucf (zerof)))) p = ncom prfNoteq6--1,2 
u_3,2,0,1,5,4 (sucf (sucf (sucf (zerof)))) (sucf (zerof)) p = prfNoteq6--1,2 

u_3,2,0,1,5,4 (sucf (zerof)) (sucf (sucf (sucf (sucf (zerof))))) p = prfNoteq6--2,5 
u_3,2,0,1,5,4 (sucf (sucf (sucf (sucf (zerof))))) (sucf (zerof)) p = ncom prfNoteq6--2,5 

u_3,2,0,1,5,4 (sucf (zerof)) (sucf (sucf (sucf (sucf (sucf (zerof)))))) p = prfNoteq6--2,4 
u_3,2,0,1,5,4 (sucf (sucf (sucf (sucf (sucf (zerof)))))) (sucf (zerof)) p = ncom prfNoteq6--2,4 

u_3,2,0,1,5,4 (sucf (sucf (zerof))) (sucf (sucf (sucf (zerof)))) p = prfNoteq6--0,1 
u_3,2,0,1,5,4 (sucf (sucf (sucf (zerof)))) (sucf (sucf (zerof))) p = ncom prfNoteq6--0,1 

u_3,2,0,1,5,4 (sucf (sucf (zerof))) (sucf (sucf (sucf (sucf (zerof))))) p = prfNoteq6--0,5 
u_3,2,0,1,5,4 (sucf (sucf (sucf (sucf (zerof))))) (sucf (sucf (zerof))) p = ncom prfNoteq6--0,5 

u_3,2,0,1,5,4 (sucf (sucf (zerof))) (sucf (sucf (sucf (sucf (sucf (zerof)))))) p = prfNoteq6--0,4 
u_3,2,0,1,5,4 (sucf (sucf (sucf (sucf (sucf (zerof)))))) (sucf (sucf (zerof))) p = ncom prfNoteq6--0,4 

u_3,2,0,1,5,4 (sucf (sucf (sucf (zerof)))) (sucf (sucf (sucf (sucf (zerof))))) p = prfNoteq6--1,5 
u_3,2,0,1,5,4 (sucf (sucf (sucf (sucf (zerof))))) (sucf (sucf (sucf (zerof)))) p = ncom prfNoteq6--1,5 

u_3,2,0,1,5,4 (sucf (sucf (sucf (zerof)))) (sucf (sucf (sucf (sucf (sucf (zerof)))))) p = prfNoteq6--1,4 
u_3,2,0,1,5,4 (sucf (sucf (sucf (sucf (sucf (zerof)))))) (sucf (sucf (sucf (zerof)))) p = ncom prfNoteq6--1,4 

u_3,2,0,1,5,4 (sucf (sucf (sucf (sucf (zerof))))) (sucf (sucf (sucf (sucf (sucf (zerof)))))) p = ncom prfNoteq6--4,5 
u_3,2,0,1,5,4 (sucf (sucf (sucf (sucf (sucf (zerof)))))) (sucf (sucf (sucf (sucf (zerof))))) p = prfNoteq6--4,5 

u_3,2,1,0,5,4 : (i j : Fin 6) → (i ≢ j) → nth p_3,2,1,0,5,4 i ≢ nth p_3,2,1,0,5,4 j 
u_3,2,1,0,5,4 (zerof) (zerof) p = ⊥-elim (p refl)
u_3,2,1,0,5,4 (sucf (zerof)) (sucf (zerof)) p = ⊥-elim (p refl)
u_3,2,1,0,5,4 (sucf (sucf (zerof))) (sucf (sucf (zerof))) p = ⊥-elim (p refl)
u_3,2,1,0,5,4 (sucf (sucf (sucf (zerof)))) (sucf (sucf (sucf (zerof)))) p = ⊥-elim (p refl)
u_3,2,1,0,5,4 (sucf (sucf (sucf (sucf (zerof))))) (sucf (sucf (sucf (sucf (zerof))))) p = ⊥-elim (p refl)
u_3,2,1,0,5,4 (sucf (sucf (sucf (sucf (sucf (zerof)))))) (sucf (sucf (sucf (sucf (sucf (zerof)))))) p = ⊥-elim (p refl)
u_3,2,1,0,5,4 (sucf (sucf (sucf (sucf (sucf (sucf h)))))) _ = ⊥-elim (nolify h) 
u_3,2,1,0,5,4 _ (sucf (sucf (sucf (sucf (sucf (sucf h)))))) = ⊥-elim (nolify h) 

u_3,2,1,0,5,4 (zerof) (sucf (zerof)) p = ncom prfNoteq6--2,3 
u_3,2,1,0,5,4 (sucf (zerof)) (zerof) p = prfNoteq6--2,3 

u_3,2,1,0,5,4 (zerof) (sucf (sucf (zerof))) p = ncom prfNoteq6--1,3 
u_3,2,1,0,5,4 (sucf (sucf (zerof))) (zerof) p = prfNoteq6--1,3 

u_3,2,1,0,5,4 (zerof) (sucf (sucf (sucf (zerof)))) p = ncom prfNoteq6--0,3 
u_3,2,1,0,5,4 (sucf (sucf (sucf (zerof)))) (zerof) p = prfNoteq6--0,3 

u_3,2,1,0,5,4 (zerof) (sucf (sucf (sucf (sucf (zerof))))) p = prfNoteq6--3,5 
u_3,2,1,0,5,4 (sucf (sucf (sucf (sucf (zerof))))) (zerof) p = ncom prfNoteq6--3,5 

u_3,2,1,0,5,4 (zerof) (sucf (sucf (sucf (sucf (sucf (zerof)))))) p = prfNoteq6--3,4 
u_3,2,1,0,5,4 (sucf (sucf (sucf (sucf (sucf (zerof)))))) (zerof) p = ncom prfNoteq6--3,4 

u_3,2,1,0,5,4 (sucf (zerof)) (sucf (sucf (zerof))) p = ncom prfNoteq6--1,2 
u_3,2,1,0,5,4 (sucf (sucf (zerof))) (sucf (zerof)) p = prfNoteq6--1,2 

u_3,2,1,0,5,4 (sucf (zerof)) (sucf (sucf (sucf (zerof)))) p = ncom prfNoteq6--0,2 
u_3,2,1,0,5,4 (sucf (sucf (sucf (zerof)))) (sucf (zerof)) p = prfNoteq6--0,2 

u_3,2,1,0,5,4 (sucf (zerof)) (sucf (sucf (sucf (sucf (zerof))))) p = prfNoteq6--2,5 
u_3,2,1,0,5,4 (sucf (sucf (sucf (sucf (zerof))))) (sucf (zerof)) p = ncom prfNoteq6--2,5 

u_3,2,1,0,5,4 (sucf (zerof)) (sucf (sucf (sucf (sucf (sucf (zerof)))))) p = prfNoteq6--2,4 
u_3,2,1,0,5,4 (sucf (sucf (sucf (sucf (sucf (zerof)))))) (sucf (zerof)) p = ncom prfNoteq6--2,4 

u_3,2,1,0,5,4 (sucf (sucf (zerof))) (sucf (sucf (sucf (zerof)))) p = ncom prfNoteq6--0,1 
u_3,2,1,0,5,4 (sucf (sucf (sucf (zerof)))) (sucf (sucf (zerof))) p = prfNoteq6--0,1 

u_3,2,1,0,5,4 (sucf (sucf (zerof))) (sucf (sucf (sucf (sucf (zerof))))) p = prfNoteq6--1,5 
u_3,2,1,0,5,4 (sucf (sucf (sucf (sucf (zerof))))) (sucf (sucf (zerof))) p = ncom prfNoteq6--1,5 

u_3,2,1,0,5,4 (sucf (sucf (zerof))) (sucf (sucf (sucf (sucf (sucf (zerof)))))) p = prfNoteq6--1,4 
u_3,2,1,0,5,4 (sucf (sucf (sucf (sucf (sucf (zerof)))))) (sucf (sucf (zerof))) p = ncom prfNoteq6--1,4 

u_3,2,1,0,5,4 (sucf (sucf (sucf (zerof)))) (sucf (sucf (sucf (sucf (zerof))))) p = prfNoteq6--0,5 
u_3,2,1,0,5,4 (sucf (sucf (sucf (sucf (zerof))))) (sucf (sucf (sucf (zerof)))) p = ncom prfNoteq6--0,5 

u_3,2,1,0,5,4 (sucf (sucf (sucf (zerof)))) (sucf (sucf (sucf (sucf (sucf (zerof)))))) p = prfNoteq6--0,4 
u_3,2,1,0,5,4 (sucf (sucf (sucf (sucf (sucf (zerof)))))) (sucf (sucf (sucf (zerof)))) p = ncom prfNoteq6--0,4 

u_3,2,1,0,5,4 (sucf (sucf (sucf (sucf (zerof))))) (sucf (sucf (sucf (sucf (sucf (zerof)))))) p = ncom prfNoteq6--4,5 
u_3,2,1,0,5,4 (sucf (sucf (sucf (sucf (sucf (zerof)))))) (sucf (sucf (sucf (sucf (zerof))))) p = prfNoteq6--4,5

----------------
-- Список состоит из перестановок;
-- с ним можно будет работать noexist-ом. 
----------------

UNI : Unicalized lis 
UNI = u_0,1,2,3,4,5 u-cons (u_1,0,2,3,4,5 u-cons (u_1,0,3,2,4,5 u-cons (u_1,2,0,3,4,5 u-cons (u_1,2,3,0,4,5 u-cons (u_1,3,0,2,4,5 u-cons (u_2,0,1,3,4,5 u-cons (u_2,0,3,1,4,5 u-cons (u_2,3,0,1,4,5 u-cons (u_3,0,1,2,4,5 u-cons (u_3,0,2,1,4,5 u-cons (u_3,1,0,2,4,5 u-cons (u_3,1,2,0,4,5 u-cons (u_3,2,0,1,4,5 u-cons (u_3,2,1,0,4,5 u-cons (u_0,1,2,3,5,4 u-cons (u_1,0,2,3,5,4 u-cons (u_1,0,3,2,5,4 u-cons (u_1,2,0,3,5,4 u-cons (u_1,2,3,0,5,4 u-cons (u_1,3,0,2,5,4 u-cons (u_2,0,1,3,5,4 u-cons (u_2,0,3,1,5,4 u-cons (u_2,3,0,1,5,4 u-cons (u_3,0,1,2,5,4 u-cons (u_3,0,2,1,5,4 u-cons (u_3,1,0,2,5,4 u-cons (u_3,1,2,0,5,4 u-cons (u_3,2,0,1,5,4 u-cons (u_3,2,1,0,5,4 u-cons u-nil)))))))))))))))))))))))))))))

----------------
-- noexist-ы разных уровней.
----------------

noex<1,0> : noexist (p_1,0,2,3,4,5 ∷ p_1,0,3,2,4,5 ∷ p_2,0,1,3,4,5 ∷ p_2,0,3,1,4,5 ∷ p_3,0,1,2,4,5 ∷ p_3,0,2,1,4,5 ∷ p_3,1,0,2,4,5 ∷ p_3,1,2,0,4,5 ∷ p_3,2,0,1,4,5 ∷ p_3,2,1,0,4,5 ∷ p_1,0,2,3,5,4 ∷ p_1,0,3,2,5,4 ∷ p_2,0,1,3,5,4 ∷ p_2,0,3,1,5,4 ∷ p_3,0,1,2,5,4 ∷ p_3,0,2,1,5,4 ∷ p_3,1,0,2,5,4 ∷ p_3,1,2,0,5,4 ∷ p_3,2,0,1,5,4 ∷ p_3,2,1,0,5,4 ∷ []) 4 
noex<1,0> = basa
        (p_1,0,2,3,4,5 ∷ p_1,0,3,2,4,5 ∷ p_2,0,1,3,4,5 ∷ p_2,0,3,1,4,5 ∷ p_3,0,1,2,4,5 ∷ p_3,0,2,1,4,5 ∷ p_3,1,0,2,4,5 ∷ p_3,1,2,0,4,5 ∷ p_3,2,0,1,4,5 ∷ p_3,2,1,0,4,5 ∷ p_1,0,2,3,5,4 ∷ p_1,0,3,2,5,4 ∷ p_2,0,1,3,5,4 ∷ p_2,0,3,1,5,4 ∷ p_3,0,1,2,5,4 ∷ p_3,0,2,1,5,4 ∷ p_3,1,0,2,5,4 ∷ p_3,1,2,0,5,4 ∷ p_3,2,0,1,5,4 ∷ p_3,2,1,0,5,4 ∷ [])
        4 (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))))))))))))))

noex<2,0> : noexist (p_1,2,0,3,4,5 ∷ p_1,3,0,2,4,5 ∷ p_2,0,1,3,4,5 ∷ p_2,3,0,1,4,5 ∷ p_3,0,1,2,4,5 ∷ p_3,0,2,1,4,5 ∷ p_3,1,0,2,4,5 ∷ p_3,1,2,0,4,5 ∷ p_3,2,0,1,4,5 ∷ p_3,2,1,0,4,5 ∷ p_1,2,0,3,5,4 ∷ p_1,3,0,2,5,4 ∷ p_2,0,1,3,5,4 ∷ p_2,3,0,1,5,4 ∷ p_3,0,1,2,5,4 ∷ p_3,0,2,1,5,4 ∷ p_3,1,0,2,5,4 ∷ p_3,1,2,0,5,4 ∷ p_3,2,0,1,5,4 ∷ p_3,2,1,0,5,4 ∷ []) 4 
noex<2,0> = basa
        (p_1,2,0,3,4,5 ∷ p_1,3,0,2,4,5 ∷ p_2,0,1,3,4,5 ∷ p_2,3,0,1,4,5 ∷ p_3,0,1,2,4,5 ∷ p_3,0,2,1,4,5 ∷ p_3,1,0,2,4,5 ∷ p_3,1,2,0,4,5 ∷ p_3,2,0,1,4,5 ∷ p_3,2,1,0,4,5 ∷ p_1,2,0,3,5,4 ∷ p_1,3,0,2,5,4 ∷ p_2,0,1,3,5,4 ∷ p_2,3,0,1,5,4 ∷ p_3,0,1,2,5,4 ∷ p_3,0,2,1,5,4 ∷ p_3,1,0,2,5,4 ∷ p_3,1,2,0,5,4 ∷ p_3,2,0,1,5,4 ∷ p_3,2,1,0,5,4 ∷ [])
        4 (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))))))))))))))

noex<3,0> : noexist (p_1,2,3,0,4,5 ∷ p_2,0,3,1,4,5 ∷ p_2,3,0,1,4,5 ∷ p_3,0,1,2,4,5 ∷ p_3,0,2,1,4,5 ∷ p_3,1,0,2,4,5 ∷ p_3,1,2,0,4,5 ∷ p_3,2,0,1,4,5 ∷ p_3,2,1,0,4,5 ∷ p_1,2,3,0,5,4 ∷ p_2,0,3,1,5,4 ∷ p_2,3,0,1,5,4 ∷ p_3,0,1,2,5,4 ∷ p_3,0,2,1,5,4 ∷ p_3,1,0,2,5,4 ∷ p_3,1,2,0,5,4 ∷ p_3,2,0,1,5,4 ∷ p_3,2,1,0,5,4 ∷ []) 4 
noex<3,0> = basa
        (p_1,2,3,0,4,5 ∷ p_2,0,3,1,4,5 ∷ p_2,3,0,1,4,5 ∷ p_3,0,1,2,4,5 ∷ p_3,0,2,1,4,5 ∷ p_3,1,0,2,4,5 ∷ p_3,1,2,0,4,5 ∷ p_3,2,0,1,4,5 ∷ p_3,2,1,0,4,5 ∷ p_1,2,3,0,5,4 ∷ p_2,0,3,1,5,4 ∷ p_2,3,0,1,5,4 ∷ p_3,0,1,2,5,4 ∷ p_3,0,2,1,5,4 ∷ p_3,1,0,2,5,4 ∷ p_3,1,2,0,5,4 ∷ p_3,2,0,1,5,4 ∷ p_3,2,1,0,5,4 ∷ [])
        4 (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))))))))))))))

noex<0,4> : noexist (p_0,1,2,3,4,5 ∷ p_1,0,2,3,4,5 ∷ p_1,0,3,2,4,5 ∷ p_1,2,0,3,4,5 ∷ p_1,2,3,0,4,5 ∷ p_1,3,0,2,4,5 ∷ p_2,0,1,3,4,5 ∷ p_2,0,3,1,4,5 ∷ p_2,3,0,1,4,5 ∷ p_3,0,1,2,4,5 ∷ p_3,0,2,1,4,5 ∷ p_3,1,0,2,4,5 ∷ p_3,1,2,0,4,5 ∷ p_3,2,0,1,4,5 ∷ p_3,2,1,0,4,5 ∷ p_0,1,2,3,5,4 ∷ p_1,0,2,3,5,4 ∷ p_1,0,3,2,5,4 ∷ p_1,2,0,3,5,4 ∷ p_1,2,3,0,5,4 ∷ p_1,3,0,2,5,4 ∷ p_2,0,1,3,5,4 ∷ p_2,0,3,1,5,4 ∷ p_2,3,0,1,5,4 ∷ p_3,0,1,2,5,4 ∷ p_3,0,2,1,5,4 ∷ p_3,1,0,2,5,4 ∷ p_3,1,2,0,5,4 ∷ p_3,2,0,1,5,4 ∷ p_3,2,1,0,5,4 ∷ []) 4 
noex<0,4> = basa
        (p_0,1,2,3,4,5 ∷ p_1,0,2,3,4,5 ∷ p_1,0,3,2,4,5 ∷ p_1,2,0,3,4,5 ∷ p_1,2,3,0,4,5 ∷ p_1,3,0,2,4,5 ∷ p_2,0,1,3,4,5 ∷ p_2,0,3,1,4,5 ∷ p_2,3,0,1,4,5 ∷ p_3,0,1,2,4,5 ∷ p_3,0,2,1,4,5 ∷ p_3,1,0,2,4,5 ∷ p_3,1,2,0,4,5 ∷ p_3,2,0,1,4,5 ∷ p_3,2,1,0,4,5 ∷ p_0,1,2,3,5,4 ∷ p_1,0,2,3,5,4 ∷ p_1,0,3,2,5,4 ∷ p_1,2,0,3,5,4 ∷ p_1,2,3,0,5,4 ∷ p_1,3,0,2,5,4 ∷ p_2,0,1,3,5,4 ∷ p_2,0,3,1,5,4 ∷ p_2,3,0,1,5,4 ∷ p_3,0,1,2,5,4 ∷ p_3,0,2,1,5,4 ∷ p_3,1,0,2,5,4 ∷ p_3,1,2,0,5,4 ∷ p_3,2,0,1,5,4 ∷ p_3,2,1,0,5,4 ∷ [])
        4 (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))))))))))))))

noex<0,5> : noexist (p_0,1,2,3,4,5 ∷ p_1,0,2,3,4,5 ∷ p_1,0,3,2,4,5 ∷ p_1,2,0,3,4,5 ∷ p_1,2,3,0,4,5 ∷ p_1,3,0,2,4,5 ∷ p_2,0,1,3,4,5 ∷ p_2,0,3,1,4,5 ∷ p_2,3,0,1,4,5 ∷ p_3,0,1,2,4,5 ∷ p_3,0,2,1,4,5 ∷ p_3,1,0,2,4,5 ∷ p_3,1,2,0,4,5 ∷ p_3,2,0,1,4,5 ∷ p_3,2,1,0,4,5 ∷ p_0,1,2,3,5,4 ∷ p_1,0,2,3,5,4 ∷ p_1,0,3,2,5,4 ∷ p_1,2,0,3,5,4 ∷ p_1,2,3,0,5,4 ∷ p_1,3,0,2,5,4 ∷ p_2,0,1,3,5,4 ∷ p_2,0,3,1,5,4 ∷ p_2,3,0,1,5,4 ∷ p_3,0,1,2,5,4 ∷ p_3,0,2,1,5,4 ∷ p_3,1,0,2,5,4 ∷ p_3,1,2,0,5,4 ∷ p_3,2,0,1,5,4 ∷ p_3,2,1,0,5,4 ∷ []) 4 
noex<0,5> = basa
        (p_0,1,2,3,4,5 ∷ p_1,0,2,3,4,5 ∷ p_1,0,3,2,4,5 ∷ p_1,2,0,3,4,5 ∷ p_1,2,3,0,4,5 ∷ p_1,3,0,2,4,5 ∷ p_2,0,1,3,4,5 ∷ p_2,0,3,1,4,5 ∷ p_2,3,0,1,4,5 ∷ p_3,0,1,2,4,5 ∷ p_3,0,2,1,4,5 ∷ p_3,1,0,2,4,5 ∷ p_3,1,2,0,4,5 ∷ p_3,2,0,1,4,5 ∷ p_3,2,1,0,4,5 ∷ p_0,1,2,3,5,4 ∷ p_1,0,2,3,5,4 ∷ p_1,0,3,2,5,4 ∷ p_1,2,0,3,5,4 ∷ p_1,2,3,0,5,4 ∷ p_1,3,0,2,5,4 ∷ p_2,0,1,3,5,4 ∷ p_2,0,3,1,5,4 ∷ p_2,3,0,1,5,4 ∷ p_3,0,1,2,5,4 ∷ p_3,0,2,1,5,4 ∷ p_3,1,0,2,5,4 ∷ p_3,1,2,0,5,4 ∷ p_3,2,0,1,5,4 ∷ p_3,2,1,0,5,4 ∷ [])
        4 (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))))))))))))))

noex<1,2> : noexist (p_0,1,2,3,4,5 ∷ p_1,0,2,3,4,5 ∷ p_1,0,3,2,4,5 ∷ p_1,2,3,0,4,5 ∷ p_2,0,1,3,4,5 ∷ p_2,0,3,1,4,5 ∷ p_3,0,1,2,4,5 ∷ p_3,0,2,1,4,5 ∷ p_3,1,2,0,4,5 ∷ p_0,1,2,3,5,4 ∷ p_1,0,2,3,5,4 ∷ p_1,0,3,2,5,4 ∷ p_1,2,3,0,5,4 ∷ p_2,0,1,3,5,4 ∷ p_2,0,3,1,5,4 ∷ p_3,0,1,2,5,4 ∷ p_3,0,2,1,5,4 ∷ p_3,1,2,0,5,4 ∷ []) 4 
noex<1,2> = basa
        (p_0,1,2,3,4,5 ∷ p_1,0,2,3,4,5 ∷ p_1,0,3,2,4,5 ∷ p_1,2,3,0,4,5 ∷ p_2,0,1,3,4,5 ∷ p_2,0,3,1,4,5 ∷ p_3,0,1,2,4,5 ∷ p_3,0,2,1,4,5 ∷ p_3,1,2,0,4,5 ∷ p_0,1,2,3,5,4 ∷ p_1,0,2,3,5,4 ∷ p_1,0,3,2,5,4 ∷ p_1,2,3,0,5,4 ∷ p_2,0,1,3,5,4 ∷ p_2,0,3,1,5,4 ∷ p_3,0,1,2,5,4 ∷ p_3,0,2,1,5,4 ∷ p_3,1,2,0,5,4 ∷ [])
        4 (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))))))))))))))

noex<1,3> : noexist (p_0,1,2,3,4,5 ∷ p_1,0,2,3,4,5 ∷ p_1,0,3,2,4,5 ∷ p_1,2,0,3,4,5 ∷ p_2,0,1,3,4,5 ∷ p_2,0,3,1,4,5 ∷ p_3,0,1,2,4,5 ∷ p_3,0,2,1,4,5 ∷ p_3,1,0,2,4,5 ∷ p_0,1,2,3,5,4 ∷ p_1,0,2,3,5,4 ∷ p_1,0,3,2,5,4 ∷ p_1,2,0,3,5,4 ∷ p_2,0,1,3,5,4 ∷ p_2,0,3,1,5,4 ∷ p_3,0,1,2,5,4 ∷ p_3,0,2,1,5,4 ∷ p_3,1,0,2,5,4 ∷ []) 4 
noex<1,3> = basa
        (p_0,1,2,3,4,5 ∷ p_1,0,2,3,4,5 ∷ p_1,0,3,2,4,5 ∷ p_1,2,0,3,4,5 ∷ p_2,0,1,3,4,5 ∷ p_2,0,3,1,4,5 ∷ p_3,0,1,2,4,5 ∷ p_3,0,2,1,4,5 ∷ p_3,1,0,2,4,5 ∷ p_0,1,2,3,5,4 ∷ p_1,0,2,3,5,4 ∷ p_1,0,3,2,5,4 ∷ p_1,2,0,3,5,4 ∷ p_2,0,1,3,5,4 ∷ p_2,0,3,1,5,4 ∷ p_3,0,1,2,5,4 ∷ p_3,0,2,1,5,4 ∷ p_3,1,0,2,5,4 ∷ [])
        4 (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))))))))))))))

noex<1,4> : noexist (p_0,1,2,3,4,5 ∷ p_1,0,2,3,4,5 ∷ p_1,0,3,2,4,5 ∷ p_1,2,0,3,4,5 ∷ p_1,2,3,0,4,5 ∷ p_1,3,0,2,4,5 ∷ p_2,0,1,3,4,5 ∷ p_2,0,3,1,4,5 ∷ p_2,3,0,1,4,5 ∷ p_3,0,1,2,4,5 ∷ p_3,0,2,1,4,5 ∷ p_3,1,0,2,4,5 ∷ p_3,1,2,0,4,5 ∷ p_3,2,0,1,4,5 ∷ p_3,2,1,0,4,5 ∷ p_0,1,2,3,5,4 ∷ p_1,0,2,3,5,4 ∷ p_1,0,3,2,5,4 ∷ p_1,2,0,3,5,4 ∷ p_1,2,3,0,5,4 ∷ p_1,3,0,2,5,4 ∷ p_2,0,1,3,5,4 ∷ p_2,0,3,1,5,4 ∷ p_2,3,0,1,5,4 ∷ p_3,0,1,2,5,4 ∷ p_3,0,2,1,5,4 ∷ p_3,1,0,2,5,4 ∷ p_3,1,2,0,5,4 ∷ p_3,2,0,1,5,4 ∷ p_3,2,1,0,5,4 ∷ []) 4 
noex<1,4> = basa
        (p_0,1,2,3,4,5 ∷ p_1,0,2,3,4,5 ∷ p_1,0,3,2,4,5 ∷ p_1,2,0,3,4,5 ∷ p_1,2,3,0,4,5 ∷ p_1,3,0,2,4,5 ∷ p_2,0,1,3,4,5 ∷ p_2,0,3,1,4,5 ∷ p_2,3,0,1,4,5 ∷ p_3,0,1,2,4,5 ∷ p_3,0,2,1,4,5 ∷ p_3,1,0,2,4,5 ∷ p_3,1,2,0,4,5 ∷ p_3,2,0,1,4,5 ∷ p_3,2,1,0,4,5 ∷ p_0,1,2,3,5,4 ∷ p_1,0,2,3,5,4 ∷ p_1,0,3,2,5,4 ∷ p_1,2,0,3,5,4 ∷ p_1,2,3,0,5,4 ∷ p_1,3,0,2,5,4 ∷ p_2,0,1,3,5,4 ∷ p_2,0,3,1,5,4 ∷ p_2,3,0,1,5,4 ∷ p_3,0,1,2,5,4 ∷ p_3,0,2,1,5,4 ∷ p_3,1,0,2,5,4 ∷ p_3,1,2,0,5,4 ∷ p_3,2,0,1,5,4 ∷ p_3,2,1,0,5,4 ∷ [])
        4 (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))))))))))))))

noex<1,5> : noexist (p_0,1,2,3,4,5 ∷ p_1,0,2,3,4,5 ∷ p_1,0,3,2,4,5 ∷ p_1,2,0,3,4,5 ∷ p_1,2,3,0,4,5 ∷ p_1,3,0,2,4,5 ∷ p_2,0,1,3,4,5 ∷ p_2,0,3,1,4,5 ∷ p_2,3,0,1,4,5 ∷ p_3,0,1,2,4,5 ∷ p_3,0,2,1,4,5 ∷ p_3,1,0,2,4,5 ∷ p_3,1,2,0,4,5 ∷ p_3,2,0,1,4,5 ∷ p_3,2,1,0,4,5 ∷ p_0,1,2,3,5,4 ∷ p_1,0,2,3,5,4 ∷ p_1,0,3,2,5,4 ∷ p_1,2,0,3,5,4 ∷ p_1,2,3,0,5,4 ∷ p_1,3,0,2,5,4 ∷ p_2,0,1,3,5,4 ∷ p_2,0,3,1,5,4 ∷ p_2,3,0,1,5,4 ∷ p_3,0,1,2,5,4 ∷ p_3,0,2,1,5,4 ∷ p_3,1,0,2,5,4 ∷ p_3,1,2,0,5,4 ∷ p_3,2,0,1,5,4 ∷ p_3,2,1,0,5,4 ∷ []) 4 
noex<1,5> = basa
        (p_0,1,2,3,4,5 ∷ p_1,0,2,3,4,5 ∷ p_1,0,3,2,4,5 ∷ p_1,2,0,3,4,5 ∷ p_1,2,3,0,4,5 ∷ p_1,3,0,2,4,5 ∷ p_2,0,1,3,4,5 ∷ p_2,0,3,1,4,5 ∷ p_2,3,0,1,4,5 ∷ p_3,0,1,2,4,5 ∷ p_3,0,2,1,4,5 ∷ p_3,1,0,2,4,5 ∷ p_3,1,2,0,4,5 ∷ p_3,2,0,1,4,5 ∷ p_3,2,1,0,4,5 ∷ p_0,1,2,3,5,4 ∷ p_1,0,2,3,5,4 ∷ p_1,0,3,2,5,4 ∷ p_1,2,0,3,5,4 ∷ p_1,2,3,0,5,4 ∷ p_1,3,0,2,5,4 ∷ p_2,0,1,3,5,4 ∷ p_2,0,3,1,5,4 ∷ p_2,3,0,1,5,4 ∷ p_3,0,1,2,5,4 ∷ p_3,0,2,1,5,4 ∷ p_3,1,0,2,5,4 ∷ p_3,1,2,0,5,4 ∷ p_3,2,0,1,5,4 ∷ p_3,2,1,0,5,4 ∷ [])
        4 (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))))))))))))))

noex<2,3> : noexist (p_0,1,2,3,4,5 ∷ p_1,0,2,3,4,5 ∷ p_1,2,0,3,4,5 ∷ p_1,3,0,2,4,5 ∷ p_2,0,1,3,4,5 ∷ p_2,3,0,1,4,5 ∷ p_3,0,1,2,4,5 ∷ p_3,1,0,2,4,5 ∷ p_3,2,0,1,4,5 ∷ p_0,1,2,3,5,4 ∷ p_1,0,2,3,5,4 ∷ p_1,2,0,3,5,4 ∷ p_1,3,0,2,5,4 ∷ p_2,0,1,3,5,4 ∷ p_2,3,0,1,5,4 ∷ p_3,0,1,2,5,4 ∷ p_3,1,0,2,5,4 ∷ p_3,2,0,1,5,4 ∷ []) 4 
noex<2,3> = basa
        (p_0,1,2,3,4,5 ∷ p_1,0,2,3,4,5 ∷ p_1,2,0,3,4,5 ∷ p_1,3,0,2,4,5 ∷ p_2,0,1,3,4,5 ∷ p_2,3,0,1,4,5 ∷ p_3,0,1,2,4,5 ∷ p_3,1,0,2,4,5 ∷ p_3,2,0,1,4,5 ∷ p_0,1,2,3,5,4 ∷ p_1,0,2,3,5,4 ∷ p_1,2,0,3,5,4 ∷ p_1,3,0,2,5,4 ∷ p_2,0,1,3,5,4 ∷ p_2,3,0,1,5,4 ∷ p_3,0,1,2,5,4 ∷ p_3,1,0,2,5,4 ∷ p_3,2,0,1,5,4 ∷ [])
        4 (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))))))))))))))

noex<2,4> : noexist (p_0,1,2,3,4,5 ∷ p_1,0,2,3,4,5 ∷ p_1,0,3,2,4,5 ∷ p_1,2,0,3,4,5 ∷ p_1,2,3,0,4,5 ∷ p_1,3,0,2,4,5 ∷ p_2,0,1,3,4,5 ∷ p_2,0,3,1,4,5 ∷ p_2,3,0,1,4,5 ∷ p_3,0,1,2,4,5 ∷ p_3,0,2,1,4,5 ∷ p_3,1,0,2,4,5 ∷ p_3,1,2,0,4,5 ∷ p_3,2,0,1,4,5 ∷ p_3,2,1,0,4,5 ∷ p_0,1,2,3,5,4 ∷ p_1,0,2,3,5,4 ∷ p_1,0,3,2,5,4 ∷ p_1,2,0,3,5,4 ∷ p_1,2,3,0,5,4 ∷ p_1,3,0,2,5,4 ∷ p_2,0,1,3,5,4 ∷ p_2,0,3,1,5,4 ∷ p_2,3,0,1,5,4 ∷ p_3,0,1,2,5,4 ∷ p_3,0,2,1,5,4 ∷ p_3,1,0,2,5,4 ∷ p_3,1,2,0,5,4 ∷ p_3,2,0,1,5,4 ∷ p_3,2,1,0,5,4 ∷ []) 4 
noex<2,4> = basa
        (p_0,1,2,3,4,5 ∷ p_1,0,2,3,4,5 ∷ p_1,0,3,2,4,5 ∷ p_1,2,0,3,4,5 ∷ p_1,2,3,0,4,5 ∷ p_1,3,0,2,4,5 ∷ p_2,0,1,3,4,5 ∷ p_2,0,3,1,4,5 ∷ p_2,3,0,1,4,5 ∷ p_3,0,1,2,4,5 ∷ p_3,0,2,1,4,5 ∷ p_3,1,0,2,4,5 ∷ p_3,1,2,0,4,5 ∷ p_3,2,0,1,4,5 ∷ p_3,2,1,0,4,5 ∷ p_0,1,2,3,5,4 ∷ p_1,0,2,3,5,4 ∷ p_1,0,3,2,5,4 ∷ p_1,2,0,3,5,4 ∷ p_1,2,3,0,5,4 ∷ p_1,3,0,2,5,4 ∷ p_2,0,1,3,5,4 ∷ p_2,0,3,1,5,4 ∷ p_2,3,0,1,5,4 ∷ p_3,0,1,2,5,4 ∷ p_3,0,2,1,5,4 ∷ p_3,1,0,2,5,4 ∷ p_3,1,2,0,5,4 ∷ p_3,2,0,1,5,4 ∷ p_3,2,1,0,5,4 ∷ [])
        4 (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))))))))))))))

noex<2,5> : noexist (p_0,1,2,3,4,5 ∷ p_1,0,2,3,4,5 ∷ p_1,0,3,2,4,5 ∷ p_1,2,0,3,4,5 ∷ p_1,2,3,0,4,5 ∷ p_1,3,0,2,4,5 ∷ p_2,0,1,3,4,5 ∷ p_2,0,3,1,4,5 ∷ p_2,3,0,1,4,5 ∷ p_3,0,1,2,4,5 ∷ p_3,0,2,1,4,5 ∷ p_3,1,0,2,4,5 ∷ p_3,1,2,0,4,5 ∷ p_3,2,0,1,4,5 ∷ p_3,2,1,0,4,5 ∷ p_0,1,2,3,5,4 ∷ p_1,0,2,3,5,4 ∷ p_1,0,3,2,5,4 ∷ p_1,2,0,3,5,4 ∷ p_1,2,3,0,5,4 ∷ p_1,3,0,2,5,4 ∷ p_2,0,1,3,5,4 ∷ p_2,0,3,1,5,4 ∷ p_2,3,0,1,5,4 ∷ p_3,0,1,2,5,4 ∷ p_3,0,2,1,5,4 ∷ p_3,1,0,2,5,4 ∷ p_3,1,2,0,5,4 ∷ p_3,2,0,1,5,4 ∷ p_3,2,1,0,5,4 ∷ []) 4 
noex<2,5> = basa
        (p_0,1,2,3,4,5 ∷ p_1,0,2,3,4,5 ∷ p_1,0,3,2,4,5 ∷ p_1,2,0,3,4,5 ∷ p_1,2,3,0,4,5 ∷ p_1,3,0,2,4,5 ∷ p_2,0,1,3,4,5 ∷ p_2,0,3,1,4,5 ∷ p_2,3,0,1,4,5 ∷ p_3,0,1,2,4,5 ∷ p_3,0,2,1,4,5 ∷ p_3,1,0,2,4,5 ∷ p_3,1,2,0,4,5 ∷ p_3,2,0,1,4,5 ∷ p_3,2,1,0,4,5 ∷ p_0,1,2,3,5,4 ∷ p_1,0,2,3,5,4 ∷ p_1,0,3,2,5,4 ∷ p_1,2,0,3,5,4 ∷ p_1,2,3,0,5,4 ∷ p_1,3,0,2,5,4 ∷ p_2,0,1,3,5,4 ∷ p_2,0,3,1,5,4 ∷ p_2,3,0,1,5,4 ∷ p_3,0,1,2,5,4 ∷ p_3,0,2,1,5,4 ∷ p_3,1,0,2,5,4 ∷ p_3,1,2,0,5,4 ∷ p_3,2,0,1,5,4 ∷ p_3,2,1,0,5,4 ∷ [])
        4 (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))))))))))))))

noex<3,4> : noexist (p_0,1,2,3,4,5 ∷ p_1,0,2,3,4,5 ∷ p_1,0,3,2,4,5 ∷ p_1,2,0,3,4,5 ∷ p_1,2,3,0,4,5 ∷ p_1,3,0,2,4,5 ∷ p_2,0,1,3,4,5 ∷ p_2,0,3,1,4,5 ∷ p_2,3,0,1,4,5 ∷ p_3,0,1,2,4,5 ∷ p_3,0,2,1,4,5 ∷ p_3,1,0,2,4,5 ∷ p_3,1,2,0,4,5 ∷ p_3,2,0,1,4,5 ∷ p_3,2,1,0,4,5 ∷ p_0,1,2,3,5,4 ∷ p_1,0,2,3,5,4 ∷ p_1,0,3,2,5,4 ∷ p_1,2,0,3,5,4 ∷ p_1,2,3,0,5,4 ∷ p_1,3,0,2,5,4 ∷ p_2,0,1,3,5,4 ∷ p_2,0,3,1,5,4 ∷ p_2,3,0,1,5,4 ∷ p_3,0,1,2,5,4 ∷ p_3,0,2,1,5,4 ∷ p_3,1,0,2,5,4 ∷ p_3,1,2,0,5,4 ∷ p_3,2,0,1,5,4 ∷ p_3,2,1,0,5,4 ∷ []) 4 
noex<3,4> = basa
        (p_0,1,2,3,4,5 ∷ p_1,0,2,3,4,5 ∷ p_1,0,3,2,4,5 ∷ p_1,2,0,3,4,5 ∷ p_1,2,3,0,4,5 ∷ p_1,3,0,2,4,5 ∷ p_2,0,1,3,4,5 ∷ p_2,0,3,1,4,5 ∷ p_2,3,0,1,4,5 ∷ p_3,0,1,2,4,5 ∷ p_3,0,2,1,4,5 ∷ p_3,1,0,2,4,5 ∷ p_3,1,2,0,4,5 ∷ p_3,2,0,1,4,5 ∷ p_3,2,1,0,4,5 ∷ p_0,1,2,3,5,4 ∷ p_1,0,2,3,5,4 ∷ p_1,0,3,2,5,4 ∷ p_1,2,0,3,5,4 ∷ p_1,2,3,0,5,4 ∷ p_1,3,0,2,5,4 ∷ p_2,0,1,3,5,4 ∷ p_2,0,3,1,5,4 ∷ p_2,3,0,1,5,4 ∷ p_3,0,1,2,5,4 ∷ p_3,0,2,1,5,4 ∷ p_3,1,0,2,5,4 ∷ p_3,1,2,0,5,4 ∷ p_3,2,0,1,5,4 ∷ p_3,2,1,0,5,4 ∷ [])
        4 (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))))))))))))))

noex<3,5> : noexist (p_0,1,2,3,4,5 ∷ p_1,0,2,3,4,5 ∷ p_1,0,3,2,4,5 ∷ p_1,2,0,3,4,5 ∷ p_1,2,3,0,4,5 ∷ p_1,3,0,2,4,5 ∷ p_2,0,1,3,4,5 ∷ p_2,0,3,1,4,5 ∷ p_2,3,0,1,4,5 ∷ p_3,0,1,2,4,5 ∷ p_3,0,2,1,4,5 ∷ p_3,1,0,2,4,5 ∷ p_3,1,2,0,4,5 ∷ p_3,2,0,1,4,5 ∷ p_3,2,1,0,4,5 ∷ p_0,1,2,3,5,4 ∷ p_1,0,2,3,5,4 ∷ p_1,0,3,2,5,4 ∷ p_1,2,0,3,5,4 ∷ p_1,2,3,0,5,4 ∷ p_1,3,0,2,5,4 ∷ p_2,0,1,3,5,4 ∷ p_2,0,3,1,5,4 ∷ p_2,3,0,1,5,4 ∷ p_3,0,1,2,5,4 ∷ p_3,0,2,1,5,4 ∷ p_3,1,0,2,5,4 ∷ p_3,1,2,0,5,4 ∷ p_3,2,0,1,5,4 ∷ p_3,2,1,0,5,4 ∷ []) 4 
noex<3,5> = basa
        (p_0,1,2,3,4,5 ∷ p_1,0,2,3,4,5 ∷ p_1,0,3,2,4,5 ∷ p_1,2,0,3,4,5 ∷ p_1,2,3,0,4,5 ∷ p_1,3,0,2,4,5 ∷ p_2,0,1,3,4,5 ∷ p_2,0,3,1,4,5 ∷ p_2,3,0,1,4,5 ∷ p_3,0,1,2,4,5 ∷ p_3,0,2,1,4,5 ∷ p_3,1,0,2,4,5 ∷ p_3,1,2,0,4,5 ∷ p_3,2,0,1,4,5 ∷ p_3,2,1,0,4,5 ∷ p_0,1,2,3,5,4 ∷ p_1,0,2,3,5,4 ∷ p_1,0,3,2,5,4 ∷ p_1,2,0,3,5,4 ∷ p_1,2,3,0,5,4 ∷ p_1,3,0,2,5,4 ∷ p_2,0,1,3,5,4 ∷ p_2,0,3,1,5,4 ∷ p_2,3,0,1,5,4 ∷ p_3,0,1,2,5,4 ∷ p_3,0,2,1,5,4 ∷ p_3,1,0,2,5,4 ∷ p_3,1,2,0,5,4 ∷ p_3,2,0,1,5,4 ∷ p_3,2,1,0,5,4 ∷ [])
        4 (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))))))))))))))

noex<4,5><1,0> : noexist (p_1,0,2,3,4,5 ∷ p_1,0,3,2,4,5 ∷ p_2,0,1,3,4,5 ∷ p_2,0,3,1,4,5 ∷ p_3,0,1,2,4,5 ∷ p_3,0,2,1,4,5 ∷ p_3,1,0,2,4,5 ∷ p_3,1,2,0,4,5 ∷ p_3,2,0,1,4,5 ∷ p_3,2,1,0,4,5 ∷ []) 3 
noex<4,5><1,0> = basa
        (p_1,0,2,3,4,5 ∷ p_1,0,3,2,4,5 ∷ p_2,0,1,3,4,5 ∷ p_2,0,3,1,4,5 ∷ p_3,0,1,2,4,5 ∷ p_3,0,2,1,4,5 ∷ p_3,1,0,2,4,5 ∷ p_3,1,2,0,4,5 ∷ p_3,2,0,1,4,5 ∷ p_3,2,1,0,4,5 ∷ [])
        3 (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))))))

noex<4,5><2,0> : noexist (p_1,2,0,3,4,5 ∷ p_1,3,0,2,4,5 ∷ p_2,0,1,3,4,5 ∷ p_2,3,0,1,4,5 ∷ p_3,0,1,2,4,5 ∷ p_3,0,2,1,4,5 ∷ p_3,1,0,2,4,5 ∷ p_3,1,2,0,4,5 ∷ p_3,2,0,1,4,5 ∷ p_3,2,1,0,4,5 ∷ []) 3 
noex<4,5><2,0> = basa
        (p_1,2,0,3,4,5 ∷ p_1,3,0,2,4,5 ∷ p_2,0,1,3,4,5 ∷ p_2,3,0,1,4,5 ∷ p_3,0,1,2,4,5 ∷ p_3,0,2,1,4,5 ∷ p_3,1,0,2,4,5 ∷ p_3,1,2,0,4,5 ∷ p_3,2,0,1,4,5 ∷ p_3,2,1,0,4,5 ∷ [])
        3 (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))))))

noex<4,5><3,0> : noexist (p_1,2,3,0,4,5 ∷ p_2,0,3,1,4,5 ∷ p_2,3,0,1,4,5 ∷ p_3,0,1,2,4,5 ∷ p_3,0,2,1,4,5 ∷ p_3,1,0,2,4,5 ∷ p_3,1,2,0,4,5 ∷ p_3,2,0,1,4,5 ∷ p_3,2,1,0,4,5 ∷ []) 3 
noex<4,5><3,0> = basa
        (p_1,2,3,0,4,5 ∷ p_2,0,3,1,4,5 ∷ p_2,3,0,1,4,5 ∷ p_3,0,1,2,4,5 ∷ p_3,0,2,1,4,5 ∷ p_3,1,0,2,4,5 ∷ p_3,1,2,0,4,5 ∷ p_3,2,0,1,4,5 ∷ p_3,2,1,0,4,5 ∷ [])
        3 (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))))))

noex<4,5><0,4> : noexist (p_0,1,2,3,4,5 ∷ p_1,0,2,3,4,5 ∷ p_1,0,3,2,4,5 ∷ p_1,2,0,3,4,5 ∷ p_1,2,3,0,4,5 ∷ p_1,3,0,2,4,5 ∷ p_2,0,1,3,4,5 ∷ p_2,0,3,1,4,5 ∷ p_2,3,0,1,4,5 ∷ p_3,0,1,2,4,5 ∷ p_3,0,2,1,4,5 ∷ p_3,1,0,2,4,5 ∷ p_3,1,2,0,4,5 ∷ p_3,2,0,1,4,5 ∷ p_3,2,1,0,4,5 ∷ []) 3 
noex<4,5><0,4> = basa
        (p_0,1,2,3,4,5 ∷ p_1,0,2,3,4,5 ∷ p_1,0,3,2,4,5 ∷ p_1,2,0,3,4,5 ∷ p_1,2,3,0,4,5 ∷ p_1,3,0,2,4,5 ∷ p_2,0,1,3,4,5 ∷ p_2,0,3,1,4,5 ∷ p_2,3,0,1,4,5 ∷ p_3,0,1,2,4,5 ∷ p_3,0,2,1,4,5 ∷ p_3,1,0,2,4,5 ∷ p_3,1,2,0,4,5 ∷ p_3,2,0,1,4,5 ∷ p_3,2,1,0,4,5 ∷ [])
        3 (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))))))

noex<4,5><0,5> : noexist (p_0,1,2,3,4,5 ∷ p_1,0,2,3,4,5 ∷ p_1,0,3,2,4,5 ∷ p_1,2,0,3,4,5 ∷ p_1,2,3,0,4,5 ∷ p_1,3,0,2,4,5 ∷ p_2,0,1,3,4,5 ∷ p_2,0,3,1,4,5 ∷ p_2,3,0,1,4,5 ∷ p_3,0,1,2,4,5 ∷ p_3,0,2,1,4,5 ∷ p_3,1,0,2,4,5 ∷ p_3,1,2,0,4,5 ∷ p_3,2,0,1,4,5 ∷ p_3,2,1,0,4,5 ∷ []) 3 
noex<4,5><0,5> = basa
        (p_0,1,2,3,4,5 ∷ p_1,0,2,3,4,5 ∷ p_1,0,3,2,4,5 ∷ p_1,2,0,3,4,5 ∷ p_1,2,3,0,4,5 ∷ p_1,3,0,2,4,5 ∷ p_2,0,1,3,4,5 ∷ p_2,0,3,1,4,5 ∷ p_2,3,0,1,4,5 ∷ p_3,0,1,2,4,5 ∷ p_3,0,2,1,4,5 ∷ p_3,1,0,2,4,5 ∷ p_3,1,2,0,4,5 ∷ p_3,2,0,1,4,5 ∷ p_3,2,1,0,4,5 ∷ [])
        3 (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))))))

noex<4,5><1,2> : noexist (p_0,1,2,3,4,5 ∷ p_1,0,2,3,4,5 ∷ p_1,0,3,2,4,5 ∷ p_1,2,3,0,4,5 ∷ p_2,0,1,3,4,5 ∷ p_2,0,3,1,4,5 ∷ p_3,0,1,2,4,5 ∷ p_3,0,2,1,4,5 ∷ p_3,1,2,0,4,5 ∷ []) 3 
noex<4,5><1,2> = basa
        (p_0,1,2,3,4,5 ∷ p_1,0,2,3,4,5 ∷ p_1,0,3,2,4,5 ∷ p_1,2,3,0,4,5 ∷ p_2,0,1,3,4,5 ∷ p_2,0,3,1,4,5 ∷ p_3,0,1,2,4,5 ∷ p_3,0,2,1,4,5 ∷ p_3,1,2,0,4,5 ∷ [])
        3 (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))))))

noex<4,5><1,3> : noexist (p_0,1,2,3,4,5 ∷ p_1,0,2,3,4,5 ∷ p_1,0,3,2,4,5 ∷ p_1,2,0,3,4,5 ∷ p_2,0,1,3,4,5 ∷ p_2,0,3,1,4,5 ∷ p_3,0,1,2,4,5 ∷ p_3,0,2,1,4,5 ∷ p_3,1,0,2,4,5 ∷ []) 3 
noex<4,5><1,3> = basa
        (p_0,1,2,3,4,5 ∷ p_1,0,2,3,4,5 ∷ p_1,0,3,2,4,5 ∷ p_1,2,0,3,4,5 ∷ p_2,0,1,3,4,5 ∷ p_2,0,3,1,4,5 ∷ p_3,0,1,2,4,5 ∷ p_3,0,2,1,4,5 ∷ p_3,1,0,2,4,5 ∷ [])
        3 (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))))))

noex<4,5><1,4> : noexist (p_0,1,2,3,4,5 ∷ p_1,0,2,3,4,5 ∷ p_1,0,3,2,4,5 ∷ p_1,2,0,3,4,5 ∷ p_1,2,3,0,4,5 ∷ p_1,3,0,2,4,5 ∷ p_2,0,1,3,4,5 ∷ p_2,0,3,1,4,5 ∷ p_2,3,0,1,4,5 ∷ p_3,0,1,2,4,5 ∷ p_3,0,2,1,4,5 ∷ p_3,1,0,2,4,5 ∷ p_3,1,2,0,4,5 ∷ p_3,2,0,1,4,5 ∷ p_3,2,1,0,4,5 ∷ []) 3 
noex<4,5><1,4> = basa
        (p_0,1,2,3,4,5 ∷ p_1,0,2,3,4,5 ∷ p_1,0,3,2,4,5 ∷ p_1,2,0,3,4,5 ∷ p_1,2,3,0,4,5 ∷ p_1,3,0,2,4,5 ∷ p_2,0,1,3,4,5 ∷ p_2,0,3,1,4,5 ∷ p_2,3,0,1,4,5 ∷ p_3,0,1,2,4,5 ∷ p_3,0,2,1,4,5 ∷ p_3,1,0,2,4,5 ∷ p_3,1,2,0,4,5 ∷ p_3,2,0,1,4,5 ∷ p_3,2,1,0,4,5 ∷ [])
        3 (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))))))

noex<4,5><1,5> : noexist (p_0,1,2,3,4,5 ∷ p_1,0,2,3,4,5 ∷ p_1,0,3,2,4,5 ∷ p_1,2,0,3,4,5 ∷ p_1,2,3,0,4,5 ∷ p_1,3,0,2,4,5 ∷ p_2,0,1,3,4,5 ∷ p_2,0,3,1,4,5 ∷ p_2,3,0,1,4,5 ∷ p_3,0,1,2,4,5 ∷ p_3,0,2,1,4,5 ∷ p_3,1,0,2,4,5 ∷ p_3,1,2,0,4,5 ∷ p_3,2,0,1,4,5 ∷ p_3,2,1,0,4,5 ∷ []) 3 
noex<4,5><1,5> = basa
        (p_0,1,2,3,4,5 ∷ p_1,0,2,3,4,5 ∷ p_1,0,3,2,4,5 ∷ p_1,2,0,3,4,5 ∷ p_1,2,3,0,4,5 ∷ p_1,3,0,2,4,5 ∷ p_2,0,1,3,4,5 ∷ p_2,0,3,1,4,5 ∷ p_2,3,0,1,4,5 ∷ p_3,0,1,2,4,5 ∷ p_3,0,2,1,4,5 ∷ p_3,1,0,2,4,5 ∷ p_3,1,2,0,4,5 ∷ p_3,2,0,1,4,5 ∷ p_3,2,1,0,4,5 ∷ [])
        3 (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))))))

noex<4,5><2,3> : noexist (p_0,1,2,3,4,5 ∷ p_1,0,2,3,4,5 ∷ p_1,2,0,3,4,5 ∷ p_1,3,0,2,4,5 ∷ p_2,0,1,3,4,5 ∷ p_2,3,0,1,4,5 ∷ p_3,0,1,2,4,5 ∷ p_3,1,0,2,4,5 ∷ p_3,2,0,1,4,5 ∷ []) 3 
noex<4,5><2,3> = basa
        (p_0,1,2,3,4,5 ∷ p_1,0,2,3,4,5 ∷ p_1,2,0,3,4,5 ∷ p_1,3,0,2,4,5 ∷ p_2,0,1,3,4,5 ∷ p_2,3,0,1,4,5 ∷ p_3,0,1,2,4,5 ∷ p_3,1,0,2,4,5 ∷ p_3,2,0,1,4,5 ∷ [])
        3 (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))))))

noex<4,5><2,4> : noexist (p_0,1,2,3,4,5 ∷ p_1,0,2,3,4,5 ∷ p_1,0,3,2,4,5 ∷ p_1,2,0,3,4,5 ∷ p_1,2,3,0,4,5 ∷ p_1,3,0,2,4,5 ∷ p_2,0,1,3,4,5 ∷ p_2,0,3,1,4,5 ∷ p_2,3,0,1,4,5 ∷ p_3,0,1,2,4,5 ∷ p_3,0,2,1,4,5 ∷ p_3,1,0,2,4,5 ∷ p_3,1,2,0,4,5 ∷ p_3,2,0,1,4,5 ∷ p_3,2,1,0,4,5 ∷ []) 3 
noex<4,5><2,4> = basa
        (p_0,1,2,3,4,5 ∷ p_1,0,2,3,4,5 ∷ p_1,0,3,2,4,5 ∷ p_1,2,0,3,4,5 ∷ p_1,2,3,0,4,5 ∷ p_1,3,0,2,4,5 ∷ p_2,0,1,3,4,5 ∷ p_2,0,3,1,4,5 ∷ p_2,3,0,1,4,5 ∷ p_3,0,1,2,4,5 ∷ p_3,0,2,1,4,5 ∷ p_3,1,0,2,4,5 ∷ p_3,1,2,0,4,5 ∷ p_3,2,0,1,4,5 ∷ p_3,2,1,0,4,5 ∷ [])
        3 (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))))))

noex<4,5><2,5> : noexist (p_0,1,2,3,4,5 ∷ p_1,0,2,3,4,5 ∷ p_1,0,3,2,4,5 ∷ p_1,2,0,3,4,5 ∷ p_1,2,3,0,4,5 ∷ p_1,3,0,2,4,5 ∷ p_2,0,1,3,4,5 ∷ p_2,0,3,1,4,5 ∷ p_2,3,0,1,4,5 ∷ p_3,0,1,2,4,5 ∷ p_3,0,2,1,4,5 ∷ p_3,1,0,2,4,5 ∷ p_3,1,2,0,4,5 ∷ p_3,2,0,1,4,5 ∷ p_3,2,1,0,4,5 ∷ []) 3 
noex<4,5><2,5> = basa
        (p_0,1,2,3,4,5 ∷ p_1,0,2,3,4,5 ∷ p_1,0,3,2,4,5 ∷ p_1,2,0,3,4,5 ∷ p_1,2,3,0,4,5 ∷ p_1,3,0,2,4,5 ∷ p_2,0,1,3,4,5 ∷ p_2,0,3,1,4,5 ∷ p_2,3,0,1,4,5 ∷ p_3,0,1,2,4,5 ∷ p_3,0,2,1,4,5 ∷ p_3,1,0,2,4,5 ∷ p_3,1,2,0,4,5 ∷ p_3,2,0,1,4,5 ∷ p_3,2,1,0,4,5 ∷ [])
        3 (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))))))

noex<4,5><3,4> : noexist (p_0,1,2,3,4,5 ∷ p_1,0,2,3,4,5 ∷ p_1,0,3,2,4,5 ∷ p_1,2,0,3,4,5 ∷ p_1,2,3,0,4,5 ∷ p_1,3,0,2,4,5 ∷ p_2,0,1,3,4,5 ∷ p_2,0,3,1,4,5 ∷ p_2,3,0,1,4,5 ∷ p_3,0,1,2,4,5 ∷ p_3,0,2,1,4,5 ∷ p_3,1,0,2,4,5 ∷ p_3,1,2,0,4,5 ∷ p_3,2,0,1,4,5 ∷ p_3,2,1,0,4,5 ∷ []) 3 
noex<4,5><3,4> = basa
        (p_0,1,2,3,4,5 ∷ p_1,0,2,3,4,5 ∷ p_1,0,3,2,4,5 ∷ p_1,2,0,3,4,5 ∷ p_1,2,3,0,4,5 ∷ p_1,3,0,2,4,5 ∷ p_2,0,1,3,4,5 ∷ p_2,0,3,1,4,5 ∷ p_2,3,0,1,4,5 ∷ p_3,0,1,2,4,5 ∷ p_3,0,2,1,4,5 ∷ p_3,1,0,2,4,5 ∷ p_3,1,2,0,4,5 ∷ p_3,2,0,1,4,5 ∷ p_3,2,1,0,4,5 ∷ [])
        3 (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))))))

noex<4,5><3,5> : noexist (p_0,1,2,3,4,5 ∷ p_1,0,2,3,4,5 ∷ p_1,0,3,2,4,5 ∷ p_1,2,0,3,4,5 ∷ p_1,2,3,0,4,5 ∷ p_1,3,0,2,4,5 ∷ p_2,0,1,3,4,5 ∷ p_2,0,3,1,4,5 ∷ p_2,3,0,1,4,5 ∷ p_3,0,1,2,4,5 ∷ p_3,0,2,1,4,5 ∷ p_3,1,0,2,4,5 ∷ p_3,1,2,0,4,5 ∷ p_3,2,0,1,4,5 ∷ p_3,2,1,0,4,5 ∷ []) 3 
noex<4,5><3,5> = basa
        (p_0,1,2,3,4,5 ∷ p_1,0,2,3,4,5 ∷ p_1,0,3,2,4,5 ∷ p_1,2,0,3,4,5 ∷ p_1,2,3,0,4,5 ∷ p_1,3,0,2,4,5 ∷ p_2,0,1,3,4,5 ∷ p_2,0,3,1,4,5 ∷ p_2,3,0,1,4,5 ∷ p_3,0,1,2,4,5 ∷ p_3,0,2,1,4,5 ∷ p_3,1,0,2,4,5 ∷ p_3,1,2,0,4,5 ∷ p_3,2,0,1,4,5 ∷ p_3,2,1,0,4,5 ∷ [])
        3 (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))))))

noex<4,5><4,5> : noexist (p_0,1,2,3,4,5 ∷ p_1,0,2,3,4,5 ∷ p_1,0,3,2,4,5 ∷ p_1,2,0,3,4,5 ∷ p_1,2,3,0,4,5 ∷ p_1,3,0,2,4,5 ∷ p_2,0,1,3,4,5 ∷ p_2,0,3,1,4,5 ∷ p_2,3,0,1,4,5 ∷ p_3,0,1,2,4,5 ∷ p_3,0,2,1,4,5 ∷ p_3,1,0,2,4,5 ∷ p_3,1,2,0,4,5 ∷ p_3,2,0,1,4,5 ∷ p_3,2,1,0,4,5 ∷ []) 3 
noex<4,5><4,5> = basa
        (p_0,1,2,3,4,5 ∷ p_1,0,2,3,4,5 ∷ p_1,0,3,2,4,5 ∷ p_1,2,0,3,4,5 ∷ p_1,2,3,0,4,5 ∷ p_1,3,0,2,4,5 ∷ p_2,0,1,3,4,5 ∷ p_2,0,3,1,4,5 ∷ p_2,3,0,1,4,5 ∷ p_3,0,1,2,4,5 ∷ p_3,0,2,1,4,5 ∷ p_3,1,0,2,4,5 ∷ p_3,1,2,0,4,5 ∷ p_3,2,0,1,4,5 ∷ p_3,2,1,0,4,5 ∷ [])
        3 (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))))))

F<4,5> : (i j : Fin 6) → (i ≢ j) → (noexist (cmpFilter i j (p_0,1,2,3,4,5 ∷ p_1,0,2,3,4,5 ∷ p_1,0,3,2,4,5 ∷ p_1,2,0,3,4,5 ∷ p_1,2,3,0,4,5 ∷ p_1,3,0,2,4,5 ∷ p_2,0,1,3,4,5 ∷ p_2,0,3,1,4,5 ∷ p_2,3,0,1,4,5 ∷ p_3,0,1,2,4,5 ∷ p_3,0,2,1,4,5 ∷ p_3,1,0,2,4,5 ∷ p_3,1,2,0,4,5 ∷ p_3,2,0,1,4,5 ∷ p_3,2,1,0,4,5 ∷ [])) 3 ⊎ noexist (cmpFilter j i (p_0,1,2,3,4,5 ∷ p_1,0,2,3,4,5 ∷ p_1,0,3,2,4,5 ∷ p_1,2,0,3,4,5 ∷ p_1,2,3,0,4,5 ∷ p_1,3,0,2,4,5 ∷ p_2,0,1,3,4,5 ∷ p_2,0,3,1,4,5 ∷ p_2,3,0,1,4,5 ∷ p_3,0,1,2,4,5 ∷ p_3,0,2,1,4,5 ∷ p_3,1,0,2,4,5 ∷ p_3,1,2,0,4,5 ∷ p_3,2,0,1,4,5 ∷ p_3,2,1,0,4,5 ∷ [])) 3) 

F<4,5> (zerof) (zerof) p = ⊥-elim (p refl)
F<4,5> (sucf (zerof)) (sucf (zerof)) p = ⊥-elim (p refl)
F<4,5> (sucf (sucf (zerof))) (sucf (sucf (zerof))) p = ⊥-elim (p refl)
F<4,5> (sucf (sucf (sucf (zerof)))) (sucf (sucf (sucf (zerof)))) p = ⊥-elim (p refl)
F<4,5> (sucf (sucf (sucf (sucf (zerof))))) (sucf (sucf (sucf (sucf (zerof))))) p = ⊥-elim (p refl)
F<4,5> (sucf (sucf (sucf (sucf (sucf (zerof)))))) (sucf (sucf (sucf (sucf (sucf (zerof)))))) p = ⊥-elim (p refl)
F<4,5> (sucf (sucf (sucf (sucf (sucf (sucf h)))))) _ = ⊥-elim (nolify h) 
F<4,5> _ (sucf (sucf (sucf (sucf (sucf (sucf h)))))) = ⊥-elim (nolify h) 

F<4,5> (zerof) (sucf (zerof)) _ = inj₂ (noex<4,5><1,0>) 
F<4,5> (sucf (zerof)) (zerof) _ = inj₁ (noex<4,5><1,0>) 

F<4,5> (zerof) (sucf (sucf (zerof))) _ = inj₂ (noex<4,5><2,0>) 
F<4,5> (sucf (sucf (zerof))) (zerof) _ = inj₁ (noex<4,5><2,0>) 

F<4,5> (zerof) (sucf (sucf (sucf (zerof)))) _ = inj₂ (noex<4,5><3,0>) 
F<4,5> (sucf (sucf (sucf (zerof)))) (zerof) _ = inj₁ (noex<4,5><3,0>) 

F<4,5> (zerof) (sucf (sucf (sucf (sucf (zerof))))) _ = inj₁ (noex<4,5><0,4>) 
F<4,5> (sucf (sucf (sucf (sucf (zerof))))) (zerof) _ = inj₂ (noex<4,5><0,4>) 

F<4,5> (zerof) (sucf (sucf (sucf (sucf (sucf (zerof)))))) _ = inj₁ (noex<4,5><0,5>) 
F<4,5> (sucf (sucf (sucf (sucf (sucf (zerof)))))) (zerof) _ = inj₂ (noex<4,5><0,5>) 

F<4,5> (sucf (zerof)) (sucf (sucf (zerof))) _ = inj₁ (noex<4,5><1,2>) 
F<4,5> (sucf (sucf (zerof))) (sucf (zerof)) _ = inj₂ (noex<4,5><1,2>) 

F<4,5> (sucf (zerof)) (sucf (sucf (sucf (zerof)))) _ = inj₁ (noex<4,5><1,3>) 
F<4,5> (sucf (sucf (sucf (zerof)))) (sucf (zerof)) _ = inj₂ (noex<4,5><1,3>) 

F<4,5> (sucf (zerof)) (sucf (sucf (sucf (sucf (zerof))))) _ = inj₁ (noex<4,5><1,4>) 
F<4,5> (sucf (sucf (sucf (sucf (zerof))))) (sucf (zerof)) _ = inj₂ (noex<4,5><1,4>) 

F<4,5> (sucf (zerof)) (sucf (sucf (sucf (sucf (sucf (zerof)))))) _ = inj₁ (noex<4,5><1,5>) 
F<4,5> (sucf (sucf (sucf (sucf (sucf (zerof)))))) (sucf (zerof)) _ = inj₂ (noex<4,5><1,5>) 

F<4,5> (sucf (sucf (zerof))) (sucf (sucf (sucf (zerof)))) _ = inj₁ (noex<4,5><2,3>) 
F<4,5> (sucf (sucf (sucf (zerof)))) (sucf (sucf (zerof))) _ = inj₂ (noex<4,5><2,3>) 

F<4,5> (sucf (sucf (zerof))) (sucf (sucf (sucf (sucf (zerof))))) _ = inj₁ (noex<4,5><2,4>) 
F<4,5> (sucf (sucf (sucf (sucf (zerof))))) (sucf (sucf (zerof))) _ = inj₂ (noex<4,5><2,4>) 

F<4,5> (sucf (sucf (zerof))) (sucf (sucf (sucf (sucf (sucf (zerof)))))) _ = inj₁ (noex<4,5><2,5>) 
F<4,5> (sucf (sucf (sucf (sucf (sucf (zerof)))))) (sucf (sucf (zerof))) _ = inj₂ (noex<4,5><2,5>) 

F<4,5> (sucf (sucf (sucf (zerof)))) (sucf (sucf (sucf (sucf (zerof))))) _ = inj₁ (noex<4,5><3,4>) 
F<4,5> (sucf (sucf (sucf (sucf (zerof))))) (sucf (sucf (sucf (zerof)))) _ = inj₂ (noex<4,5><3,4>) 

F<4,5> (sucf (sucf (sucf (zerof)))) (sucf (sucf (sucf (sucf (sucf (zerof)))))) _ = inj₁ (noex<4,5><3,5>) 
F<4,5> (sucf (sucf (sucf (sucf (sucf (zerof)))))) (sucf (sucf (sucf (zerof)))) _ = inj₂ (noex<4,5><3,5>) 

F<4,5> (sucf (sucf (sucf (sucf (zerof))))) (sucf (sucf (sucf (sucf (sucf (zerof)))))) _ = inj₁ (noex<4,5><4,5>) 
F<4,5> (sucf (sucf (sucf (sucf (sucf (zerof)))))) (sucf (sucf (sucf (sucf (zerof))))) _ = inj₂ (noex<4,5><4,5>) 

noex<4,5> : noexist (p_0,1,2,3,4,5 ∷ p_1,0,2,3,4,5 ∷ p_1,0,3,2,4,5 ∷ p_1,2,0,3,4,5 ∷ p_1,2,3,0,4,5 ∷ p_1,3,0,2,4,5 ∷ p_2,0,1,3,4,5 ∷ p_2,0,3,1,4,5 ∷ p_2,3,0,1,4,5 ∷ p_3,0,1,2,4,5 ∷ p_3,0,2,1,4,5 ∷ p_3,1,0,2,4,5 ∷ p_3,1,2,0,4,5 ∷ p_3,2,0,1,4,5 ∷ p_3,2,1,0,4,5 ∷ []) 4
noex<4,5> = pereh (p_0,1,2,3,4,5 ∷ p_1,0,2,3,4,5 ∷ p_1,0,3,2,4,5 ∷ p_1,2,0,3,4,5 ∷ p_1,2,3,0,4,5 ∷ p_1,3,0,2,4,5 ∷ p_2,0,1,3,4,5 ∷ p_2,0,3,1,4,5 ∷ p_2,3,0,1,4,5 ∷ p_3,0,1,2,4,5 ∷ p_3,0,2,1,4,5 ∷ p_3,1,0,2,4,5 ∷ p_3,1,2,0,4,5 ∷ p_3,2,0,1,4,5 ∷ p_3,2,1,0,4,5 ∷ []) 3 F<4,5>

F : (i j : Fin 6) → (i ≢ j) → (noexist (cmpFilter i j (p_0,1,2,3,4,5 ∷ p_1,0,2,3,4,5 ∷ p_1,0,3,2,4,5 ∷ p_1,2,0,3,4,5 ∷ p_1,2,3,0,4,5 ∷ p_1,3,0,2,4,5 ∷ p_2,0,1,3,4,5 ∷ p_2,0,3,1,4,5 ∷ p_2,3,0,1,4,5 ∷ p_3,0,1,2,4,5 ∷ p_3,0,2,1,4,5 ∷ p_3,1,0,2,4,5 ∷ p_3,1,2,0,4,5 ∷ p_3,2,0,1,4,5 ∷ p_3,2,1,0,4,5 ∷ p_0,1,2,3,5,4 ∷ p_1,0,2,3,5,4 ∷ p_1,0,3,2,5,4 ∷ p_1,2,0,3,5,4 ∷ p_1,2,3,0,5,4 ∷ p_1,3,0,2,5,4 ∷ p_2,0,1,3,5,4 ∷ p_2,0,3,1,5,4 ∷ p_2,3,0,1,5,4 ∷ p_3,0,1,2,5,4 ∷ p_3,0,2,1,5,4 ∷ p_3,1,0,2,5,4 ∷ p_3,1,2,0,5,4 ∷ p_3,2,0,1,5,4 ∷ p_3,2,1,0,5,4 ∷ [])) 4 ⊎ noexist (cmpFilter j i (p_0,1,2,3,4,5 ∷ p_1,0,2,3,4,5 ∷ p_1,0,3,2,4,5 ∷ p_1,2,0,3,4,5 ∷ p_1,2,3,0,4,5 ∷ p_1,3,0,2,4,5 ∷ p_2,0,1,3,4,5 ∷ p_2,0,3,1,4,5 ∷ p_2,3,0,1,4,5 ∷ p_3,0,1,2,4,5 ∷ p_3,0,2,1,4,5 ∷ p_3,1,0,2,4,5 ∷ p_3,1,2,0,4,5 ∷ p_3,2,0,1,4,5 ∷ p_3,2,1,0,4,5 ∷ p_0,1,2,3,5,4 ∷ p_1,0,2,3,5,4 ∷ p_1,0,3,2,5,4 ∷ p_1,2,0,3,5,4 ∷ p_1,2,3,0,5,4 ∷ p_1,3,0,2,5,4 ∷ p_2,0,1,3,5,4 ∷ p_2,0,3,1,5,4 ∷ p_2,3,0,1,5,4 ∷ p_3,0,1,2,5,4 ∷ p_3,0,2,1,5,4 ∷ p_3,1,0,2,5,4 ∷ p_3,1,2,0,5,4 ∷ p_3,2,0,1,5,4 ∷ p_3,2,1,0,5,4 ∷ [])) 4) 

F (zerof) (zerof) p = ⊥-elim (p refl)
F (sucf (zerof)) (sucf (zerof)) p = ⊥-elim (p refl)
F (sucf (sucf (zerof))) (sucf (sucf (zerof))) p = ⊥-elim (p refl)
F (sucf (sucf (sucf (zerof)))) (sucf (sucf (sucf (zerof)))) p = ⊥-elim (p refl)
F (sucf (sucf (sucf (sucf (zerof))))) (sucf (sucf (sucf (sucf (zerof))))) p = ⊥-elim (p refl)
F (sucf (sucf (sucf (sucf (sucf (zerof)))))) (sucf (sucf (sucf (sucf (sucf (zerof)))))) p = ⊥-elim (p refl)
F (sucf (sucf (sucf (sucf (sucf (sucf h)))))) _ = ⊥-elim (nolify h) 
F _ (sucf (sucf (sucf (sucf (sucf (sucf h)))))) = ⊥-elim (nolify h) 

F (zerof) (sucf (zerof)) _ = inj₂ (noex<1,0>) 
F (sucf (zerof)) (zerof) _ = inj₁ (noex<1,0>) 

F (zerof) (sucf (sucf (zerof))) _ = inj₂ (noex<2,0>) 
F (sucf (sucf (zerof))) (zerof) _ = inj₁ (noex<2,0>) 

F (zerof) (sucf (sucf (sucf (zerof)))) _ = inj₂ (noex<3,0>) 
F (sucf (sucf (sucf (zerof)))) (zerof) _ = inj₁ (noex<3,0>) 

F (zerof) (sucf (sucf (sucf (sucf (zerof))))) _ = inj₁ (noex<0,4>) 
F (sucf (sucf (sucf (sucf (zerof))))) (zerof) _ = inj₂ (noex<0,4>) 

F (zerof) (sucf (sucf (sucf (sucf (sucf (zerof)))))) _ = inj₁ (noex<0,5>) 
F (sucf (sucf (sucf (sucf (sucf (zerof)))))) (zerof) _ = inj₂ (noex<0,5>) 

F (sucf (zerof)) (sucf (sucf (zerof))) _ = inj₁ (noex<1,2>) 
F (sucf (sucf (zerof))) (sucf (zerof)) _ = inj₂ (noex<1,2>) 

F (sucf (zerof)) (sucf (sucf (sucf (zerof)))) _ = inj₁ (noex<1,3>) 
F (sucf (sucf (sucf (zerof)))) (sucf (zerof)) _ = inj₂ (noex<1,3>) 

F (sucf (zerof)) (sucf (sucf (sucf (sucf (zerof))))) _ = inj₁ (noex<1,4>) 
F (sucf (sucf (sucf (sucf (zerof))))) (sucf (zerof)) _ = inj₂ (noex<1,4>) 

F (sucf (zerof)) (sucf (sucf (sucf (sucf (sucf (zerof)))))) _ = inj₁ (noex<1,5>) 
F (sucf (sucf (sucf (sucf (sucf (zerof)))))) (sucf (zerof)) _ = inj₂ (noex<1,5>) 

F (sucf (sucf (zerof))) (sucf (sucf (sucf (zerof)))) _ = inj₁ (noex<2,3>) 
F (sucf (sucf (sucf (zerof)))) (sucf (sucf (zerof))) _ = inj₂ (noex<2,3>) 

F (sucf (sucf (zerof))) (sucf (sucf (sucf (sucf (zerof))))) _ = inj₁ (noex<2,4>) 
F (sucf (sucf (sucf (sucf (zerof))))) (sucf (sucf (zerof))) _ = inj₂ (noex<2,4>) 

F (sucf (sucf (zerof))) (sucf (sucf (sucf (sucf (sucf (zerof)))))) _ = inj₁ (noex<2,5>) 
F (sucf (sucf (sucf (sucf (sucf (zerof)))))) (sucf (sucf (zerof))) _ = inj₂ (noex<2,5>) 

F (sucf (sucf (sucf (zerof)))) (sucf (sucf (sucf (sucf (zerof))))) _ = inj₁ (noex<3,4>) 
F (sucf (sucf (sucf (sucf (zerof))))) (sucf (sucf (sucf (zerof)))) _ = inj₂ (noex<3,4>) 

F (sucf (sucf (sucf (zerof)))) (sucf (sucf (sucf (sucf (sucf (zerof)))))) _ = inj₁ (noex<3,5>) 
F (sucf (sucf (sucf (sucf (sucf (zerof)))))) (sucf (sucf (sucf (zerof)))) _ = inj₂ (noex<3,5>) 

F (sucf (sucf (sucf (sucf (zerof))))) (sucf (sucf (sucf (sucf (sucf (zerof)))))) _ = inj₁ (noex<4,5>) 
F (sucf (sucf (sucf (sucf (sucf (zerof)))))) (sucf (sucf (sucf (sucf (zerof))))) _ = inj₂ (noex<4,5>)

----------------
-- Не существует алгоритма сортировки
-- глубиной не больше 5.
----------------

noex : noexist (p_0,1,2,3,4,5 ∷ p_1,0,2,3,4,5 ∷ p_1,0,3,2,4,5 ∷ p_1,2,0,3,4,5 ∷ p_1,2,3,0,4,5 ∷ p_1,3,0,2,4,5 ∷ p_2,0,1,3,4,5 ∷ p_2,0,3,1,4,5 ∷ p_2,3,0,1,4,5 ∷ p_3,0,1,2,4,5 ∷ p_3,0,2,1,4,5 ∷ p_3,1,0,2,4,5 ∷ p_3,1,2,0,4,5 ∷ p_3,2,0,1,4,5 ∷ p_3,2,1,0,4,5 ∷ p_0,1,2,3,5,4 ∷ p_1,0,2,3,5,4 ∷ p_1,0,3,2,5,4 ∷ p_1,2,0,3,5,4 ∷ p_1,2,3,0,5,4 ∷ p_1,3,0,2,5,4 ∷ p_2,0,1,3,5,4 ∷ p_2,0,3,1,5,4 ∷ p_2,3,0,1,5,4 ∷ p_3,0,1,2,5,4 ∷ p_3,0,2,1,5,4 ∷ p_3,1,0,2,5,4 ∷ p_3,1,2,0,5,4 ∷ p_3,2,0,1,5,4 ∷ p_3,2,1,0,5,4 ∷ []) 5
noex = pereh (p_0,1,2,3,4,5 ∷ p_1,0,2,3,4,5 ∷ p_1,0,3,2,4,5 ∷ p_1,2,0,3,4,5 ∷ p_1,2,3,0,4,5 ∷ p_1,3,0,2,4,5 ∷ p_2,0,1,3,4,5 ∷ p_2,0,3,1,4,5 ∷ p_2,3,0,1,4,5 ∷ p_3,0,1,2,4,5 ∷ p_3,0,2,1,4,5 ∷ p_3,1,0,2,4,5 ∷ p_3,1,2,0,4,5 ∷ p_3,2,0,1,4,5 ∷ p_3,2,1,0,4,5 ∷ p_0,1,2,3,5,4 ∷ p_1,0,2,3,5,4 ∷ p_1,0,3,2,5,4 ∷ p_1,2,0,3,5,4 ∷ p_1,2,3,0,5,4 ∷ p_1,3,0,2,5,4 ∷ p_2,0,1,3,5,4 ∷ p_2,0,3,1,5,4 ∷ p_2,3,0,1,5,4 ∷ p_3,0,1,2,5,4 ∷ p_3,0,2,1,5,4 ∷ p_3,1,0,2,5,4 ∷ p_3,1,2,0,5,4 ∷ p_3,2,0,1,5,4 ∷ p_3,2,1,0,5,4 ∷ []) 4 F

noalgprf : (a : Alg lis) → (depth a ℕ≤ 5) → ⊥ 
noalgprf = noexistNoAlg (s≤s (s≤s z≤n)) UNI noex

----------------
-- Но существует глубиной побольше.
----------------

autoalg : Alg lis
autoalg = node (zerof) (sucf (zerof)) prfNoteq6--0,1 
        (node (zerof) (sucf (sucf (zerof))) prfNoteq6--0,2 
                (node (zerof) (sucf (sucf (sucf (zerof)))) prfNoteq6--0,3 
                        (node (sucf (sucf (sucf (sucf (zerof))))) (sucf (sucf (sucf (sucf (sucf (zerof)))))) prfNoteq6--4,5 
                                (leaf p_0,1,2,3,4,5)
                                (leaf p_0,1,2,3,5,4))
                        (node (sucf (sucf (sucf (sucf (zerof))))) (sucf (sucf (sucf (sucf (sucf (zerof)))))) prfNoteq6--4,5 
                                (leaf p_1,2,3,0,4,5)
                                (leaf p_1,2,3,0,5,4)))
                (node (zerof) (sucf (sucf (sucf (zerof)))) prfNoteq6--0,3 
                        (node (sucf (zerof)) (sucf (sucf (sucf (zerof)))) prfNoteq6--1,3 
                                (node (sucf (sucf (sucf (sucf (zerof))))) (sucf (sucf (sucf (sucf (sucf (zerof)))))) prfNoteq6--4,5 
                                        (leaf p_1,2,0,3,4,5)
                                        (leaf p_1,2,0,3,5,4))
                                (node (sucf (sucf (sucf (sucf (zerof))))) (sucf (sucf (sucf (sucf (sucf (zerof)))))) prfNoteq6--4,5 
                                        (leaf p_1,3,0,2,4,5)
                                        (leaf p_1,3,0,2,5,4)))
                        (node (sucf (sucf (sucf (sucf (zerof))))) (sucf (sucf (sucf (sucf (sucf (zerof)))))) prfNoteq6--4,5 
                                (leaf p_2,3,0,1,4,5)
                                (leaf p_2,3,0,1,5,4))))
        (node (zerof) (sucf (sucf (zerof))) prfNoteq6--0,2 
                (node (zerof) (sucf (sucf (sucf (zerof)))) prfNoteq6--0,3 
                        (node (sucf (sucf (zerof))) (sucf (sucf (sucf (zerof)))) prfNoteq6--2,3 
                                (node (sucf (sucf (sucf (sucf (zerof))))) (sucf (sucf (sucf (sucf (sucf (zerof)))))) prfNoteq6--4,5 
                                        (leaf p_1,0,2,3,4,5)
                                        (leaf p_1,0,2,3,5,4))
                                (node (sucf (sucf (sucf (sucf (zerof))))) (sucf (sucf (sucf (sucf (sucf (zerof)))))) prfNoteq6--4,5 
                                        (leaf p_1,0,3,2,4,5)
                                        (leaf p_1,0,3,2,5,4)))
                        (node (sucf (sucf (sucf (sucf (zerof))))) (sucf (sucf (sucf (sucf (sucf (zerof)))))) prfNoteq6--4,5 
                                (leaf p_2,0,3,1,4,5)
                                (leaf p_2,0,3,1,5,4)))
                (node (zerof) (sucf (sucf (sucf (zerof)))) prfNoteq6--0,3 
                        (node (sucf (sucf (sucf (sucf (zerof))))) (sucf (sucf (sucf (sucf (sucf (zerof)))))) prfNoteq6--4,5 
                                (leaf p_2,0,1,3,4,5)
                                (leaf p_2,0,1,3,5,4))
                        (node (sucf (zerof)) (sucf (sucf (zerof))) prfNoteq6--1,2 
                                (node (sucf (zerof)) (sucf (sucf (sucf (zerof)))) prfNoteq6--1,3 
                                        (node (sucf (sucf (zerof))) (sucf (sucf (sucf (zerof)))) prfNoteq6--2,3 
                                                (node (sucf (sucf (sucf (sucf (zerof))))) (sucf (sucf (sucf (sucf (sucf (zerof)))))) prfNoteq6--4,5 
                                                        (leaf p_3,0,1,2,4,5)
                                                        (leaf p_3,0,1,2,5,4))
                                                (node (sucf (sucf (sucf (sucf (zerof))))) (sucf (sucf (sucf (sucf (sucf (zerof)))))) prfNoteq6--4,5 
                                                        (leaf p_3,0,2,1,4,5)
                                                        (leaf p_3,0,2,1,5,4)))
                                        (node (sucf (sucf (sucf (sucf (zerof))))) (sucf (sucf (sucf (sucf (sucf (zerof)))))) prfNoteq6--4,5 
                                                (leaf p_3,1,2,0,4,5)
                                                (leaf p_3,1,2,0,5,4)))
                                (node (sucf (zerof)) (sucf (sucf (sucf (zerof)))) prfNoteq6--1,3 
                                        (node (sucf (sucf (sucf (sucf (zerof))))) (sucf (sucf (sucf (sucf (sucf (zerof)))))) prfNoteq6--4,5 
                                                (leaf p_3,1,0,2,4,5)
                                                (leaf p_3,1,0,2,5,4))
                                        (node (sucf (sucf (zerof))) (sucf (sucf (sucf (zerof)))) prfNoteq6--2,3 
                                                (node (sucf (sucf (sucf (sucf (zerof))))) (sucf (sucf (sucf (sucf (sucf (zerof)))))) prfNoteq6--4,5 
                                                        (leaf p_3,2,0,1,4,5)
                                                        (leaf p_3,2,0,1,5,4))
                                                (node (sucf (sucf (sucf (sucf (zerof))))) (sucf (sucf (sucf (sucf (sucf (zerof)))))) prfNoteq6--4,5 
                                                        (leaf p_3,2,1,0,4,5)
                                                        (leaf p_3,2,1,0,5,4)))))))
