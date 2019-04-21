{-# OPTIONS --without-K --safe #-}
module Propositional where

open import Data.Nat
open import Data.List
open import Data.List.Relation.Unary.All
open import Function

infixl 60 ~_
infixl 50 _∧_
infixl 40 _∨_
infixl 30 _⇒_
infixl 20 _⇔_
infixl 10 _⊢_

pattern [_,_] y z = y ∷ z ∷ []
pattern [_,_,_] x y z = x ∷ y ∷ z ∷ []
pattern [_,_,_,_] w x y z = w ∷ x ∷ y ∷ z ∷ []
pattern [_,_,_,_,_] v w x y z = v ∷ w ∷ x ∷ y ∷ z ∷ []
pattern [_,_,_,_,_,_] u v w x y z = u ∷ v ∷ w ∷ x ∷ y ∷ z ∷ []

data PL : Set where
  ⊤ : PL
  ⊥ : PL
  Var : ℕ → PL
  ~_ : PL → PL
  _∧_ : PL → PL → PL
  _∨_ : PL → PL → PL
  _⇒_ : PL → PL → PL
  _⇔_ : PL → PL → PL

data _⊢_ : List PL → PL → Set where
  ~-intro : (p q : PL) → [ p ⇒ q , p ⇒ ~ q ] ⊢ ~ p
  ~-elim : (p q : PL) → [ ~ p ] ⊢ p ⇒ q
  ~~-elim : (p : PL) → [ ~ ~ p ] ⊢ p
  ∧-intro : (p q : PL) → [ p , q ] ⊢ p ∧ q
  ∧-elim₁ : (p q : PL) → [ p ∧ q ] ⊢ p
  ∧-elim₂ : (p q : PL) → [ p ∧ q ] ⊢ q
  ∨-intro₁ : (p q : PL) → [ p ] ⊢ p ∨ q
  ∨-intro₂ : (p q : PL) → [ q ] ⊢ p ∨ q
  ∨-elim : (p q r : PL) → [ p ∨ q , p ⇒ r , q ⇒ r ] ⊢ r
  ⇔-intro : (p q : PL) → [ p ⇒ q , q ⇒ p ] ⊢ p ⇔ q
  ⇔-elim₁ : (p q : PL) → [ p ⇔ q ] ⊢ p ⇒ q
  ⇔-elim₂ : (p q : PL) → [ p ⇔ q ] ⊢ q ⇒ p
  ⇒-intro : (p q : PL) (Δ : List PL) → ((p ∷ Δ) ⊢ q) → (Δ ⊢ p ⇒ q)
  ⇒-elim : (p q : PL) → [ p , p ⇒ q ] ⊢ q
  -- weakening : ∀ Γ A Σ → Γ ⊢ Σ → (A ∷ Γ) ⊢ Σ
  -- contraction : ∀ Γ A Σ → (A ∷ A ∷ Γ) ⊢ Σ → (A ∷ Γ) ⊢ Σ

project : ∀ {Γ C} → Γ ⊢ C → PL
project {Γ} {C} ent = C

-- Δ ⊢ p, p ⊢ q → Δ ⊢ q
weaken : ∀ {Γ} Δ C → Δ ⊢ C → (Γ ++ Δ) ⊢ C
weaken Δ C = {!   !}

-- need to transform p, p ⇒ q ⊢ q INTO Δ ⊢ p, Δ ⊢ p ⇒ q ⊢ Δ ⊢ q
lift : ∀ {Γ} Δ C → Γ ⊢ C → All (λ x → Δ ⊢ x) Γ → Δ ⊢ C
lift Δ C p1 p2 = {!   !}

assume : ∀ P {Γ C} → (P ∷ Γ) ⊢ C → Γ ⊢ (P ⇒ C)
assume P {Γ} {C} = ⇒-intro P C Γ

liftedMP : ∀ Γ p q → Γ ⊢ p → Γ ⊢ p ⇒ q → Γ ⊢ q
liftedMP Γ p q = {!   !}

⊢-comp : (p q : PL) (Δ : List PL) → Δ ⊢ p → (p ∷ Δ) ⊢ q → Δ ⊢ q
⊢-comp p q Δ Δ⊢p p+Δ⊢q = {! assume p (p+Δ⊢q)  !}

excludedMiddle : (p : PL) → [] ⊢ p ∨ ~ p
excludedMiddle p = {! ~~-elim (p ∨ ~ p)  !}
