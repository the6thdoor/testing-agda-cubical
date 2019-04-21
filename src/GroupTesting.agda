{-# OPTIONS --cubical --safe #-}
module GroupTesting where

open import Cubical.Core.Everything
open import Cubical.Data.Everything
import AbstractAlgebra as AA
open import Function using (case_of_; case_return_of_)

data ℤ₂ : Set where
  zero : ℤ₂
  one : ℤ₂

_∘_ : ℤ₂ → ℤ₂ → ℤ₂
zero ∘ zero = zero
zero ∘ one = one
one ∘ zero = one
one ∘ one = zero

assoc : AA.Associative _∘_
assoc zero zero zero = refl
assoc zero zero one = refl
assoc zero one zero = refl
assoc zero one one = refl
assoc one zero zero = refl
assoc one zero one = refl
assoc one one zero = refl
assoc one one one = refl

idL : AA.LeftIdentity zero _∘_
idL zero = refl
idL one = refl

idR : AA.RightIdentity zero _∘_
idR zero = refl
idR one = refl

grpℤ₂ : AA.Group ℤ₂ _∘_
grpℤ₂ = record
  { assoc = assoc
  ; e = zero
  ; left-id = idL
  ; right-id = idR
  ; -_ = Function.id
  ; left-inv = λ x → case x return (λ y → y ∘ y ≡ zero) of λ { zero → refl ; one → refl }
  ; right-inv = λ x → case x return (λ y → y ∘ y ≡ zero) of λ { zero → refl ; one → refl }
  }
