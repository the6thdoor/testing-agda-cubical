{-# OPTIONS --cubical --safe #-}
module SequentBase where

open import PL
open import Data.List
open import Function

infixl 10 _⊢_

pattern [_,_] y z = y ∷ z ∷ []
pattern [_,_,_] x y z = x ∷ y ∷ z ∷ []
pattern [_,_,_,_] w x y z = w ∷ x ∷ y ∷ z ∷ []
pattern [_,_,_,_,_] v w x y z = v ∷ w ∷ x ∷ y ∷ z ∷ []
pattern [_,_,_,_,_,_] u v w x y z = u ∷ v ∷ w ∷ x ∷ y ∷ z ∷ []

-- Rules of natural deduction [classical propositional logic]
data _⊢_ : List PL → PL → Set where
  assumption : ∀ {Γ} p → (p ∷ Γ) ⊢ p
  ⊤-intro : ∀ {Γ} → Γ ⊢ ⊤
  ⊥-elim : ∀ {Γ} p → Γ ⊢ ⊥ → Γ ⊢ p
  ~-intro : ∀ {Γ} p {q} → Γ ⊢ p ⇒ q → Γ ⊢ p ⇒ ~ q → Γ ⊢ ~ p
  ~-elim : ∀ {Γ} p q → Γ ⊢ (~ p) → Γ ⊢ (p ⇒ q)
  ~~-elim : ∀ {Γ} p → Γ ⊢ ~ ~ p → Γ ⊢ p -- CLASSICAL LOGIC ONLY, Implies LEM, non-contradiction
  ∧-intro : ∀ {Γ} p q → Γ ⊢ p → Γ ⊢ q → Γ ⊢ p ∧ q
  ∧-elim₁ : ∀ {Γ} p q → Γ ⊢ p ∧ q → Γ ⊢ p
  ∧-elim₂ : ∀ {Γ} p q → Γ ⊢ p ∧ q → Γ ⊢ q
  ∨-intro₁ : ∀ {Γ} p q → Γ ⊢ p → Γ ⊢ p ∨ q
  ∨-intro₂ : ∀ {Γ} p q → Γ ⊢ q → Γ ⊢ p ∨ q
  ∨-elim : ∀ {Γ} p q r → Γ ⊢ p ∨ q → Γ ⊢ p ⇒ r → Γ ⊢ q ⇒ r → Γ ⊢ r
  ⇔-intro : ∀ {Γ} p q → Γ ⊢ p ⇒ q → Γ ⊢ q ⇒ p → Γ ⊢ p ⇔ q
  ⇔-elim₁ : ∀ {Γ} p q → Γ ⊢ p ⇔ q → Γ ⊢ p ⇒ q
  ⇔-elim₂ : ∀ {Γ} p q → Γ ⊢ p ⇔ q → Γ ⊢ q ⇒ p
  ⇒-intro : ∀ {Γ} p {q} → (p ∷ Γ) ⊢ q → Γ ⊢ (p ⇒ q)
  ⇒-elim : ∀ {Γ} p q → Γ ⊢ p ⇒ q → Γ ⊢ p → Γ ⊢ q
  weaken : ∀ {Γ} p {q} → Γ ⊢ q → (p ∷ Γ) ⊢ q
  contract : ∀ {Γ} p {q} → (p ∷ p ∷ Γ) ⊢ q → (p ∷ Γ) ⊢ q
  exchange : ∀ {Γ} p q {r} → (p ∷ q ∷ Γ) ⊢ r → (q ∷ p ∷ Γ) ⊢ r

Tautology : PL → Set
Tautology P = ∀ {Γ} → Γ ⊢ P

⇒-bind : ∀ {Γ a b} → Γ ⊢ a → (a ∷ Γ) ⊢ b → Γ ⊢ b
⇒-bind {Γ} {a} {b} p1 p2 = ⇒-elim a b (⇒-intro a p2) p1

_>>=_ : ∀ {Γ a b} → Γ ⊢ a → (a ∷ Γ) ⊢ b → Γ ⊢ b
_>>=_ = ⇒-bind

⊢-move : ∀ {Γ} p q → Γ ⊢ p ⇒ q → (p ∷ Γ) ⊢ q
⊢-move p q proof = ⇒-elim p q (weaken p proof) (assumption p)

contradiction : ∀ {Γ} p q → Γ ⊢ p ⇒ (q ∧ ~ q) → Γ ⊢ ~ p
contradiction p q proof = ~-intro p {q} (⇒-intro p {q} (∧-elim₁ q (~ q) (⇒-elim p (q ∧ ~ q) (weaken p proof) (assumption p)))) (⇒-intro p {~ q} ((∧-elim₂ q (~ q) (⇒-elim p (q ∧ ~ q) (weaken p proof) (assumption p)))))

contradiction-axiom : ∀ {Γ} p → Γ ⊢ ~ (p ∧ ~ p)
contradiction-axiom p = contradiction (p ∧ ~ p) p (⇒-intro (p ∧ ~ p) (assumption (p ∧ ~ p)))

explosion : ∀ {Γ} p q → Γ ⊢ p ∧ ~ p → Γ ⊢ q
explosion p q proof = ⇒-elim (p ∧ ~ p) q (~-elim (p ∧ ~ p) q (contradiction-axiom p)) proof

lem : ∀ {Γ} p → Γ ⊢ p ∨ ~ p
lem p = ~~-elim (p ∨ ~ p) (~-intro (~ (p ∨ ~ p)) (⇒-intro (~ (p ∨ ~ p)) (∨-intro₂ p (~ p) (contradiction p (p ∨ ~ p) (⇒-intro p (∧-intro (p ∨ ~ p) (~ (p ∨ ~ p)) (∨-intro₁ p (~ p) (assumption p)) (weaken p (assumption (~ (p ∨ ~ p))))))))) (⇒-intro (~ (p ∨ ~ p)) (assumption (~ (p ∨ ~ p)))))

⇔-replace₁ : ∀ Γ p q → Γ ⊢ p ⇔ q → Γ ⊢ p → Γ ⊢ q
⇔-replace₁ Γ p q p⇔q proof = ⇒-elim p q (⇔-elim₁ p q p⇔q) proof

⇔-replace₂ : ∀ Γ p q → Γ ⊢ p ⇔ q → Γ ⊢ q → Γ ⊢ p
⇔-replace₂ Γ p q p⇔q proof = ⇒-elim q p (⇔-elim₂ p q p⇔q) proof

∧-comm : ∀ {Γ} p q → Γ ⊢ p ∧ q ⇔ q ∧ p
∧-comm p q = ⇔-intro (p ∧ q) (q ∧ p) (⇒-intro (p ∧ q) (∧-intro q p (∧-elim₂ p q (assumption (p ∧ q))) (∧-elim₁ p q (assumption (p ∧ q))))) (⇒-intro (q ∧ p) (∧-intro p q (∧-elim₂ q p (assumption (q ∧ p))) (∧-elim₁ q p (assumption (q ∧ p)))))

∨-comm : ∀ {Γ} p q → Γ ⊢ p ∨ q ⇔ q ∨ p
∨-comm p q = ⇔-intro (p ∨ q) (q ∨ p) (⇒-intro (p ∨ q) (∨-elim p q (q ∨ p) (assumption (p ∨ q)) (⇒-intro p (∨-intro₂ q p (assumption p))) (⇒-intro q (∨-intro₁ q p (assumption q))))) (⇒-intro (q ∨ p) (∨-elim q p (p ∨ q) (assumption (q ∨ p)) (⇒-intro q (∨-intro₂ p q (assumption q))) (⇒-intro p (∨-intro₁ p q (assumption p)))))

⇒-refl : ∀ {Γ} p → Γ ⊢ p ⇒ p
⇒-refl p = ⇒-intro p (assumption p)

⇒-trans : ∀ {Γ} p q r → Γ ⊢ p ⇒ q → Γ ⊢ q ⇒ r → Γ ⊢ p ⇒ r
⇒-trans p q r p1 p2 = ⇒-intro p (⇒-elim q r (weaken p p2) (⇒-elim p q (weaken p p1) (assumption p)))

⇔-refl : ∀ {Γ} p → Γ ⊢ p ⇔ p
⇔-refl p = ⇔-intro p p (⇒-intro p (assumption p)) (⇒-intro p (assumption p))

⇔-sym : ∀ {Γ} p q → Γ ⊢ p ⇔ q → Γ ⊢ q ⇔ p
⇔-sym p q proof = ⇔-intro q p (⇔-elim₂ p q proof) (⇔-elim₁ p q proof)

⇔-trans : ∀ {Γ} p q r → Γ ⊢ p ⇔ q → Γ ⊢ q ⇔ r → Γ ⊢ p ⇔ r
⇔-trans p q r p1 p2 = ⇔-intro p r (⇒-trans p q r (⇔-elim₁ p q p1) (⇔-elim₁ q r p2)) (⇒-trans r q p (⇔-elim₂ q r p2) (⇔-elim₂ p q p1))

constructive-dilemma : ∀ Γ p q r s → Γ ⊢ p ∨ q → Γ ⊢ p ⇒ r → Γ ⊢ q ⇒ s → Γ ⊢ r ∨ s
constructive-dilemma Γ p q r s p∨q p⇒r q⇒s = ∨-elim p q (r ∨ s) p∨q (⇒-intro p (∨-intro₁ r s (⇒-elim p r (weaken p p⇒r) (assumption p)))) (⇒-intro q (∨-intro₂ r s (⇒-elim q s (weaken q q⇒s) (assumption q))))

~~-intro : ∀ {Γ} p → Γ ⊢ p → Γ ⊢ ~ ~ p
~~-intro p proof = contradiction (~ p) p (⇒-intro (~ p) (∧-intro p (~ p) (weaken (~ p) proof) (assumption (~ p))))

inferenceIs⇒ : ∀ p q → (f : ∀ {Γ} → Γ ⊢ p → Γ ⊢ q) → (∀ {Γ} → Γ ⊢ p ⇒ q)
inferenceIs⇒ p q f = ⇒-intro p (f (assumption p))

doubleInferenceIs⇔ : ∀ p q (f : ∀ {Γ} → Γ ⊢ p → Γ ⊢ q) (g : ∀ {Γ} → Γ ⊢ q → Γ ⊢ p) → (∀ {Γ} → Γ ⊢ p ⇔ q)
doubleInferenceIs⇔ p q f g = ⇔-intro p q (inferenceIs⇒ p q f) (inferenceIs⇒ q p g)

disjunctive-syllogism : ∀ {Γ} p q → Γ ⊢ p ∨ q → Γ ⊢ ~ p → Γ ⊢ q
disjunctive-syllogism p q p∨q proof = ∨-elim p q q p∨q (~-elim p q proof) (⇒-intro q (assumption q))

material-implication : ∀ {Γ} p q → Γ ⊢ (p ⇒ q) ⇔ (~ p ∨ q)
material-implication {Γ} p q = ⇔-intro (p ⇒ q) (~ p ∨ q)
  (⇒-intro (p ⇒ q) (constructive-dilemma (p ⇒ q ∷ Γ) (~ p) p (~ p) q (⇔-replace₁ (p ⇒ q ∷ Γ) (p ∨ ~ p) (~ p ∨ p) (∨-comm p (~ p)) (weaken (p ⇒ q) (lem p))) (⇒-intro (~ p) (assumption (~ p))) (assumption (p ⇒ q))))
  (⇒-intro (~ p ∨ q) (⇒-intro p (disjunctive-syllogism (~ p) q (weaken p (assumption (~ p ∨ q))) (~~-intro p (assumption p)))))

contraEquiv⊥ : ∀ {Γ} p → Γ ⊢ p ∧ ~ p ⇔ ⊥
contraEquiv⊥ p = ⇔-intro (p ∧ ~ p) ⊥ (inferenceIs⇒ (p ∧ ~ p) ⊥ (explosion p ⊥)) (inferenceIs⇒ ⊥ (p ∧ ~ p) λ {Γ} → ⊥-elim (p ∧ ~ p))

~~-⇔ : ∀ {Γ} p → Γ ⊢ p ⇔ ~ ~ p
~~-⇔ p = doubleInferenceIs⇔ p (~ ~ p) (~~-intro p) (~~-elim p)

bivalence : ∀ {Γ} p → Γ ⊢ (p ⇔ ⊤) ∨ (p ⇔ ⊥)
bivalence {Γ} p = constructive-dilemma Γ p (~ p) (p ⇔ ⊤) (p ⇔ ⊥) (lem p) (⇒-intro p (⇔-intro p ⊤ (⇒-intro p ⊤-intro) (⇒-intro ⊤ (weaken ⊤ (assumption p))))) (⇒-intro (~ p) (⇔-intro p ⊥ (~-elim p ⊥ (assumption (~ p))) (⇒-intro ⊥ (⊥-elim p (assumption ⊥)))))

⇒-cong : ∀ {Γ} p q (f : PL → PL) → (sound : ∀ {Δ} x → Δ ⊢ x ⇒ f x) → Γ ⊢ p ⇒ q → Γ ⊢ f p ⇒ f q
⇒-cong {Γ} p q f f⇒ proof = ⇔-replace₂ Γ (f p ⇒ f q) (~ f p ∨ f q)
  (material-implication (f p) (f q)) (⇒-elim (~ f p) (~ f p ∨ f q) (⇒-intro (~ f p) (∨-intro₁ (~ f p) (f q) (assumption (~ f p)))) (⇔-replace₂ Γ (~ f p) (p ⇒ q) (⇔-intro (~ f p) (p ⇒ q) (⇒-intro (~ f p) (weaken (~ f p) proof)) (⇒-intro (p ⇒ q) {!   !})) proof))

⇔-cong : ∀ {Γ} p q (f : PL → PL) → (sound : ∀ {Δ} x → Δ ⊢ x ⇒ f x) → Γ ⊢ p ⇔ q → Γ ⊢ f p ⇔ f q
⇔-cong p q f f⇒ proof = ⇔-intro (f p) (f q) (⇒-cong p q f f⇒ (⇔-elim₁ p q proof)) (⇒-cong q p f f⇒ (⇔-elim₂ p q proof))

bad : [] ⊢ ⊥
bad = {!   !}

-- ?????????????????????????????????????? Did I do something wrong??? Why does this proof take so long?
contraposition : ∀ {Γ} p q → Γ ⊢ (p ⇒ q) ⇔ (~ q ⇒ ~ p)
contraposition {Γ} p q = ⇔-trans (p ⇒ q) (~ p ∨ q) (~ q ⇒ ~ p) (material-implication p q)
  (⇔-sym (~ q ⇒ ~ p) (~ p ∨ q) (⇔-trans (~ q ⇒ ~ p) (q ∨ ~ p) (~ p ∨ q) (⇔-trans (~ q ⇒ ~ p) (~ ~ q ∨ ~ p) (q ∨ ~ p) (material-implication (~ q) (~ p)) (⇔-intro (~ (~ q) ∨ ~ p) (q ∨ ~ p) (⇒-intro (~ (~ q) ∨ ~ p)
    (∨-elim (~ (~ q)) (~ p) (q ∨ ~ p) (assumption (~ (~ q) ∨ ~ p)) (⇒-intro (~ (~ q)) (∨-intro₁ q (~ p) (~~-elim q (assumption (~ (~ q)))))) (⇒-intro (~ p) (∨-intro₂ q (~ p) (assumption (~ p)))))) (⇒-intro (q ∨ ~ p) (∨-elim q (~ p) (~ (~ q) ∨ ~ p) (assumption (q ∨ ~ p)) (⇒-intro q (∨-intro₁ (~ (~ q)) (~ p) (~~-intro q (assumption q)))) (⇒-intro (~ p) (∨-intro₂ (~ (~ q)) (~ p) (assumption (~ p)))))))) (∨-comm q (~ p))))

deMorgan₁ : ∀ {Γ} p q → Γ ⊢ ~ (p ∧ q) ⇔ (~ p ∨ ~ q)
deMorgan₁ {Γ} p q = ⇔-intro (~ (p ∧ q)) (~ p ∨ ~ q) (⇒-intro (~ (p ∧ q)) (⇔-replace₁ (~ (p ∧ q) ∷ Γ) (p ⇒ ~ q) (~ p ∨ ~ q) (material-implication p (~ q))
 (⇒-intro p (contradiction q (p ∧ q) (⇒-intro q (∧-intro (p ∧ q) (~ (p ∧ q)) (∧-intro p q (weaken q (assumption p)) (assumption q)) (weaken q $ weaken p $ assumption (~ (p ∧ q)))))))))
 (⇒-intro (~ p ∨ ~ q) (contradiction (p ∧ q) q (⇒-intro (p ∧ q) (∧-intro q (~ q) (∧-elim₂ p q (assumption (p ∧ q))) (disjunctive-syllogism (~ p) (~ q) (weaken (p ∧ q) (assumption (~ p ∨ ~ q))) (~~-intro p (∧-elim₁ p q (assumption (p ∧ q)))))))))

deMorgan₂ : ∀ {Γ} p q → Γ ⊢ ~ (p ∨ q) ⇔ (~ p ∧ ~ q)
deMorgan₂ {Γ} p q = ⇔-intro (~ (p ∨ q)) (~ p ∧ ~ q)
  (⇒-intro (~ (p ∨ q)) (∧-intro (~ p) (~ q) (contradiction p (p ∨ q) (⇒-intro p (∧-intro (p ∨ q) (~ (p ∨ q)) (∨-intro₁ p q (assumption p)) (weaken p (assumption (~ (p ∨ q))))))) (contradiction q (p ∨ q) (⇒-intro q (∧-intro (p ∨ q) (~ (p ∨ q)) (∨-intro₂ p q (assumption q)) (weaken q (assumption (~ (p ∨ q)))))))))
  {!  !}
