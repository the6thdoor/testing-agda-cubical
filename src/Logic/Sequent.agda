{-# OPTIONS --cubical --safe #-}
module Sequent where

open import PL
open import Cubical.HITs.ListedFiniteSet
open import Cubical.Foundations.Prelude renaming (_∧_ to _∧C_; _∨_ to _∨C_; ~_ to ~C_)
open import Cubical.Core.Everything renaming (_∧_ to _∧C_; _∨_ to _∨C_; ~_ to ~C_)
open import Function
import Cubical.Foundations.Isomorphism as Iso
open import Cubical.Relation.Nullary
open import Cubical.Relation.Nullary.DecidableEq

infixl 10 _⊢_

data _⊢_ : LFSet PL → PL → Set where
  -- assumption : ∀ p → [ p ] ⊢ p
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
  ⇒-intro : ∀ {Γ} p {q} → (p ∷ Γ ⊢ q) → (Γ ⊢ p ⇒ q)
  ⇒-elim : ∀ {Γ} p q → Γ ⊢ p ⇒ q → Γ ⊢ p → Γ ⊢ q
  weaken : ∀ {Γ p q} → (Γ ⊢ q) → (p ∷ Γ ⊢ q)
  setEquality : ∀ {Γ Δ p} → Γ ⊢ p → Γ ≡ Δ → Δ ⊢ p -- ⇒ contract, exchange, consider removing this for substructural logics

genAssumption : ∀ Γ p → {! _∈_  !} → Γ ⊢ p
genAssumption Γ p p∈Γ = {!   !}

contract : ∀ Γ p {q} → p ∷ p ∷ Γ ⊢ q → p ∷ Γ ⊢ q
contract Γ p proof = setEquality proof (dup p Γ)

exchange : ∀ Γ p q {r} → p ∷ q ∷ Γ ⊢ r → q ∷ p ∷ Γ ⊢ r
exchange Γ p q proof = setEquality proof (comm p q Γ)

assumptions : ∀ {Γ C} → Γ ⊢ C → LFSet PL
assumptions {Γ} {C} pf = Γ

weakenEquality : ∀ Γ p q → p ∷ p ∷ Γ ⊢ q ≡ p ∷ Γ ⊢ q
weakenEquality Γ p q = Iso.isoToPath (Iso.iso (contract Γ p) weaken {!   !} {!   !})

-- transportEvidence : ∀ {Γ p q} →

-- ⊢isSet : ∀ Γ P → isSet (Γ ⊢ P)
-- ⊢isSet Γ P ⊢₁ ⊢₂ ≡₁ ≡₂ = {! Discrete→isSet  !}

-- transportEvidence : ∀ Γ Δ C → Γ ≡ Δ → Γ ⊢ C → Δ ⊢ C
-- transportEvidence Γ Δ C Γ≡Δ Γ⊢C = subst (_⊢ C) Γ≡Δ Γ⊢C

-- equivalentEvidence : ∀ {Γ Δ} C → Γ ≡ Δ → Γ ⊢ C ≡ Δ ⊢ C
-- equivalentEvidence C Γ≡Δ = cong (_⊢ C) Γ≡Δ

-- equivalence : ∀ Γ C X → (X ∷ Γ) ⊢ C ≃ (X ∷ Γ) ⊢ C
-- equivalence Γ C X = (contract ∘ weaken) , (record { equiv-proof = λ y → (y , {!   !}) , (λ y₁ i → {!   !} , {!   !}) })

weakenList' : ∀ Γ C → [] ⊢ C → Γ ⊢ C
weakenList' [] C proof = proof
weakenList' (x ∷ Γ) C proof = weaken (weakenList' Γ C proof)
weakenList' (dup x Γ i) C proof = {! weaken (weakenList' Γ)  !}
  -- where p : (λ i → dup x Γ i ⊢ C) [ weaken (weaken (weakenList' Γ C proof)) ≡ weaken (weakenList' Γ C proof) ]
  --       p i = {! weakenList' Γ C proof  !}
weakenList' (comm x y Γ i) C proof = {!   !}
weakenList' (trunc Γ Γ₁ x y i i₁) C proof = {!   !}

-- evidenceEquality : {Γ Δ : LFSet PL} (p : Γ ⊢ p) (q : Δ ⊢ p) → Γ ≡ Δ → Γ ⊢ P ≡ Δ ⊢ P
-- evidenceEquality {Γ} {Δ} P setEquality = cong (_⊢ P) (setEquality)

weakenMany' : ∀ Γ Δ C → Γ ⊢ C → (Δ ++ Γ) ⊢ C
weakenMany' Γ [] C proof = proof
weakenMany' Γ (x ∷ Δ) C proof = weaken (weakenMany' Γ Δ C proof)
weakenMany' Γ (dup x Δ i) C proof = {! weaken (weakenMany' ? ? C proof)  !}
weakenMany' Γ (comm x y Δ i) C proof = {!   !}
weakenMany' Γ (trunc Δ Δ₁ x y i i₁) C proof = {!   !}

sequent-moving : ∀ Γ p q → Γ ⊢ p ⇒ q → p ∷ Γ ⊢ q
sequent-moving Γ p q proof = ⇒-elim p q (weaken proof) {!   !}
