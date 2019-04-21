{-# OPTIONS --cubical --safe #-}
module FiniteGroup where

open import Cubical.Core.Everything
open import Cubical.Data.Nat
open import Cubical.Data.Prod
open import Data.Fin
open import AbstractAlgebra
open import Function using (case_of_)

-- Finite Group k is the group defined by the set Fin k and two operations:
--   ∘ : Fin k → Fin k → Fin k
--   - : Fin k → Fin k

FiniteGroup : (n : ℕ) (_∘_ : Fin n → Fin n → Fin n) → Set
FiniteGroup n _∘_ = Group (Fin n) _∘_

_%_ : Fin 2 → Fin 2 → Fin 2
zero % zero = zero
suc zero % zero = suc zero
zero % suc zero = suc zero
suc zero % suc zero = zero

%-assoc : Associative _%_
%-assoc zero zero zero = refl
%-assoc (suc zero) zero zero = refl
%-assoc zero (suc zero) zero = refl
%-assoc (suc zero) (suc zero) zero = refl
%-assoc zero zero (suc zero) = refl
%-assoc (suc zero) zero (suc zero) = refl
%-assoc zero (suc zero) (suc zero) = refl
%-assoc (suc zero) (suc zero) (suc zero) = refl

%-0-idL : LeftIdentity zero _%_
%-0-idL zero = refl
%-0-idL (suc zero) = refl

%-0-idR : RightIdentity zero _%_
%-0-idR zero = refl
%-0-idR (suc zero) = refl

self-inv : ∀ x → x % x ≡ zero
self-inv zero = refl
self-inv (suc zero) = refl

grp2 : FiniteGroup 2 _%_
grp2 = record
  { assoc = %-assoc
  ; e = zero
  ; left-id = %-0-idL
  ; right-id = %-0-idR
  ; -_ = λ x → x
  ; left-inv = self-inv
  ; right-inv = self-inv
  }

funcSet : {A B : Set} (f : A → B) → A × B
funcSet f = ?

grp2-op-unique : ∀ f g → FiniteGroup 2 f ≃ FiniteGroup 2 g
grp2-op-unique f g = {!   !}
