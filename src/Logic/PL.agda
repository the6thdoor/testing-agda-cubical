{-# OPTIONS --cubical --safe #-}
module PL where

open import Data.Nat
open import Data.List
-- open import Cubical.Foundations.Prelude renaming (_∧_ to _∧C_; _∨_ to _∨C_; ~_ to ~C_)
open import Cubical.Core.Everything renaming (_∧_ to _∧C_; _∨_ to _∨C_; ~_ to ~C_)

infixl 60 ~_
infixl 50 _∧_
infixl 40 _∨_
infixl 30 _⇒_
infixl 20 _⇔_

data PL : Set where
  ⊤ : PL
  ⊥ : PL
  Var : ℕ → PL
  ~_ : PL → PL
  _∧_ : PL → PL → PL
  _∨_ : PL → PL → PL
  _⇒_ : PL → PL → PL
  _⇔_ : PL → PL → PL
