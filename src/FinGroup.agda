{-# OPTIONS --cubical --safe #-}
module FinGroup where

open import Cubical.Core.Everything
open import Cubical.Data.Nat
open import Cubical.Relation.Nullary
open import Cubical.Data.Empty
open import AbstractAlgebra
open import Data.Fin
open import Function using (case_of_)

data FinGroup : (n : ℕ) → (_∘_ : Fin n → Fin n → Fin n) → (-_ : Fin n → Fin n) → Associative _∘_ → Set where
  el : ∀ {n _∘_ -_ pf} → Fin n → FinGroup n _∘_ -_ pf

¬FinGroup0 : ∀ {f g pf} → ¬ FinGroup 0 f g pf
¬FinGroup0 (el ())

record FiniteGroup (n : ℕ) : Set where
  field
    e : Fin n
    op : Fin n → Fin n → Fin n
    neg : Fin n → Fin n
    op-assoc : Associative op
    left-id : LeftIdentity e op
    right-id : RightIdentity e op
    neg-inv-left : (x : Fin n) → op (neg x) x ≡ e
    neg-inv-right : (x : Fin n) → op x (neg x) ≡ e

finiteGroup-is-group : ∀ {n} → (x : FiniteGroup n) → Group (Fin n) (FiniteGroup.op x)
finiteGroup-is-group grp = record
  { assoc = FiniteGroup.op-assoc grp
  ; e = FiniteGroup.e grp
  ; left-id = FiniteGroup.left-id grp
  ; right-id = FiniteGroup.right-id grp
  ; -_ = FiniteGroup.neg grp
  ; left-inv = FiniteGroup.neg-inv-left grp
  ; right-inv = FiniteGroup.neg-inv-right grp
  }

-- fromFin : (n : ℕ) → (_∘_ : Fin n → Fin n → Fin n) → (-_ : Fin n → Fin n) → Associative _∘_ → ()

_∘_ : Fin 2 → Fin 2 → Fin 2
zero ∘ zero = zero
suc zero ∘ zero = suc zero
zero ∘ suc zero = suc zero
suc zero ∘ suc zero = zero

-_ : Fin 2 → Fin 2
- zero = zero
- suc zero = suc zero

two-op-assoc : Associative _∘_
two-op-assoc zero zero zero = refl
two-op-assoc zero zero (suc zero) = refl
two-op-assoc zero (suc zero) zero = refl
two-op-assoc zero (suc zero) (suc zero) = refl
two-op-assoc (suc zero) zero zero = refl
two-op-assoc (suc zero) zero (suc zero) = refl
two-op-assoc (suc zero) (suc zero) zero = refl
two-op-assoc (suc zero) (suc zero) (suc zero) = refl

left-id-op : LeftIdentity zero _∘_
left-id-op zero = refl
left-id-op (suc zero) = refl

right-id-op : RightIdentity zero _∘_
right-id-op zero = refl
right-id-op (suc zero) = refl

neg-inv-left-minus : ∀ x → (- x) ∘ x ≡ zero
neg-inv-left-minus zero = refl
neg-inv-left-minus (suc zero) = refl

neg-inv-right-minus : ∀ x → x ∘ (- x) ≡ zero
neg-inv-right-minus zero = refl
neg-inv-right-minus (suc zero) = refl

FiniteGroup2 : FiniteGroup 2
FiniteGroup2 = record
  { e = zero
  ; op = _∘_
  ; neg = -_
  ; op-assoc = two-op-assoc
  ; left-id = left-id-op
  ; right-id = right-id-op
  ; neg-inv-left = neg-inv-left-minus
  ; neg-inv-right = neg-inv-right-minus
  }

finGroup2-unique : (G H : FiniteGroup 2) → G Iso H
finGroup2-unique G H = {!   !}
