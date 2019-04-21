{-# OPTIONS --cubical --safe #-}
module FiniteGroup where

open import Cubical.Core.Everything
open import Cubical.Data.Nat
open import Cubical.Relation.Nullary
open import Cubical.Data.Empty
open import AbstractAlgebra

-- FiniteGroup k should be the group (Fin k, ∘), where ∘ : Fin k → Fin k → Fin k and ∘ associative.
-- FiniteGroup k should have the minimal structure sufficient to show that it is in fact a group.

data FiniteGroup : ℕ → Set where
  e : {n : ℕ} → FiniteGroup (suc n)
  _∘_ : {n : ℕ} → FiniteGroup (suc n) → FiniteGroup (suc n) → FiniteGroup (suc n)

-_ : {n : ℕ} → FiniteGroup (suc n) → FiniteGroup (suc n)
- a = {!   !}

no-group-of-order-zero : ¬ FiniteGroup 0
no-group-of-order-zero ()

trivial-group : (x : FiniteGroup 1) → x ≡ e
trivial-group e = refl
trivial-group (x ∘ x₁) = {!   !}

-- GOAL
finGroup-is-group : {n : ℕ} → Group (FiniteGroup (suc n)) _∘_
finGroup-is-group = record
  { assoc = {!   !}
  ; e = e
  ; left-id = {!   !}
  ; right-id = {!   !}
  ; -_ = -_
  ; left-inv = {!   !}
  ; right-inv = {!   !}
  }
