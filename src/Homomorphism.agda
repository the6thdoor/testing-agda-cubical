{-# OPTIONS --cubical --safe #-}
module Homomorphism where

open import Cubical.Core.Everything
open import AbstractAlgebra

data _::_↝_ {A B : Set} {_∘₁_ _∘₂_} (f : A → B) (G : Group A _∘₁_) (H : Group B _∘₂_): Set where
  hom-def : ∀ x y → f (x ∘₁ y) ≡ (f x) ∘₂ (f y) → f :: G ↝ H

G :
