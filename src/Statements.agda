{-# OPTIONS --cubical --safe #-}
module Statements where

open import Cubical.Core.Everything
open import Cubical.Data.Nat
open import Cubical.Relation.Nullary
open import Cubical.Data.Empty
open import AbstractAlgebra

semigroup-ℕ : Semigroup ℕ _+_
semigroup-ℕ = record { assoc = +-assoc }

monoid-ℕ : Monoid ℕ _+_
monoid-ℕ = record { assoc = +-assoc ; e = 0 ; left-id = λ x → refl ; right-id = λ x → sym (+-comm 0 x) }

-- The below would be read as the following in traditional set theory:
-- Prop: Let + be the unique binary operation on ⊘. Then (⊘, +) is not a group.
-- Suppose to the contrary that ⊘ is a group. Then there exists e ∈ ⊘ such that for all x ∈ ⊘, e + x = x + e = x.
-- Then ⊘ is non-empty, a contradiction.
-- Therefore, ⊘ is not a group. ∎
⊘-not-group : ∀ {_+_} → ¬ Group ⊥ _+_
⊘-not-group = λ x → ⊥-elim (Group.e x)
