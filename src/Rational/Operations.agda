{-# OPTIONS --cubical --safe #-}
module Operations where

open import Cubical.Core.Everything
open import Cubical.HITs.Rational
open import Cubical.HITs.HitInt
open import Cubical.Relation.Nullary
open import Cubical.Data.Empty

-- Rationals are constructed by the function con : (num denom : ℤ) → ¬ denom ≡ 0 → ℚ.
-- Addition:
-- a / b + c / d = ?
-- a / b + c / d
-- (a / b) (d / d) + (b / b) (c / d)
-- ad / bd + bc / bd = ad + bc / bd

nonzero-mult : (a b : ℤ) → ¬ a ≡ pos 0 → ¬ b ≡ pos 0 → ¬ (a *ℤ b) ≡ pos 0
nonzero-mult a b ¬a≡0 ¬b≡0 = {! _↦_  !}

_+_ : ℚ → ℚ → ℚ
con a b x + con c d x₁ = con ((a *ℤ d) +ℤ (b *ℤ c)) (b *ℤ d) {!   !}
con u a x + path u₁ a₁ v b x₁ i = {!   !}
con u a x + trunc b b₁ x₁ y i i₁ = {!   !}
path u a v b₁ x i + b = {!   !}
trunc a a₁ x y i i₁ + b = {!   !}
