{-# OPTIONS --cubical --safe #-}
module AbstractAlgebra where

open import Cubical.Core.Everything
open import Cubical.Data.Nat
open import Cubical.Relation.Nullary
open import Cubical.Data.Empty

-- Some nice looking helper types

Associative : {A : Set} (f : A → A → A) → Set
Associative f = ∀ x y z → f x (f y z) ≡ f (f x y) z

Commutative : {A : Set} (f : A → A → A) → Set
Commutative f = ∀ x y → f x y ≡ f y x

_DistributiveOver_ : {A : Set} (f g : A → A → A) → Set
f DistributiveOver g = ∀ x y z → f z (g x y) ≡ g (f z x) (f z y)

LeftIdentity : {A : Set} (e : A) (f : A → A → A) → Set
LeftIdentity e f = ∀ x → f e x ≡ x

RightIdentity : {A : Set} (e : A) (f : A → A → A) → Set
RightIdentity e f = ∀ x → f x e ≡ x

-- Algebraic structures

record Semigroup (A : Set) (f : A → A → A) : Set where
  field
    assoc : Associative f

record Monoid (A : Set) (f : A → A → A) : Set where
  field
    assoc : Associative f
    e : A
    left-id : LeftIdentity e f
    right-id : RightIdentity e f

record Group (A : Set) (f : A → A → A) : Set where
  field
    assoc : Associative f
    e : A
    left-id : LeftIdentity e f
    right-id : RightIdentity e f
    -_ : A → A
    left-inv : ∀ x → f (- x) x ≡ e
    right-inv : ∀ x → f x (- x) ≡ e

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

-- data FinGroup : ℕ → Set where
--   e : ∀ {n} → FinGroup (suc n)
--   _∘_ : ∀ {n} → FinGroup n → FinGroup n → FinGroup n
