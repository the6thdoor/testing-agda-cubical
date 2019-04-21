module PropLogic where

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
  ~-intro : ∀ {Γ} p {q} → Γ ⊢ p ⇒ q → Γ ⊢ p ⇒ ~ q → Γ ⊢ ~ p
  ~-elim : ∀ {Γ} p q → Γ ⊢ (~ p) → Γ ⊢ (p ⇒ q)
  ~~-elim : ∀ {Γ} p → Γ ⊢ ~ ~ p → Γ ⊢ p -- CLASSICAL LOGIC ONLY
  ∧-intro : ∀ {Γ} p q → Γ ⊢ p → Γ ⊢ q → Γ ⊢ p ∧ q
  ∧-elim₁ : ∀ {Γ} p q → Γ ⊢ p ∧ q → Γ ⊢ p
  ∧-elim₂ : ∀ {Γ} p q → Γ ⊢ p ∧ q → Γ ⊢ q
  ∨-intro₁ : ∀ {Γ} p q → Γ ⊢ p → Γ ⊢ p ∨ q
  ∨-intro₂ : ∀ {Γ} p q → Γ ⊢ q → Γ ⊢ p ∨ q
  ∨-elim : ∀ {Γ} p q r → Γ ⊢ p ∨ q → Γ ⊢ p ⇒ r → Γ ⊢ q ⇒ r → Γ ⊢ r
  ⇔-intro : ∀ {Γ} p q → Γ ⊢ p ⇒ q → Γ ⊢ q ⇒ p → Γ ⊢ p ⇔ q
  ⇔-elim₁ : ∀ {Γ} p q → Γ ⊢ p ⇔ q → Γ ⊢ p ⇒ q
  ⇔-elim₂ : ∀ {Γ} p q → Γ ⊢ p ⇔ q → Γ ⊢ q ⇒ p
  ⇒-intro : ∀ {Γ} p {q} → (Γ ⊢ p → Γ ⊢ q) → (Γ ⊢ p ⇒ q)
  ⇒-elim : ∀ {Γ} p q → Γ ⊢ p → Γ ⊢ p ⇒ q → Γ ⊢ q


⊢_ : PL → Set
⊢ p = [] ⊢ p

contradiction : ∀ {Γ} p q → Γ ⊢ p ⇒ (q ∧ ~ q) → Γ ⊢ ~ p
contradiction p q c = ~-intro p {q}
  (⇒-intro p λ ⊢p → ∧-elim₁ q (~ q) (⇒-elim p (q ∧ ~ q) ⊢p c))
  (⇒-intro p (λ ⊢p → ∧-elim₂ q (~ q) (⇒-elim p (q ∧ ~ q) ⊢p c)))

lem : ∀ p → ⊢ p ∨ ~ p
lem p = ~~-elim {[]} (p ∨ ~ p) (~-intro (~ (p ∨ ~ p)) (⇒-intro (~ (p ∨ ~ p)) {p} {!   !}) (⇒-intro (~ (p ∨ ~ p)) {!   !}))
