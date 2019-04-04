{-# OPTIONS --cubical --safe #-}
module AbstractAlgebra where

open import Cubical.Core.Everything

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
