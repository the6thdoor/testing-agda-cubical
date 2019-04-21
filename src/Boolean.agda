{-# OPTIONS --cubical --safe #-}
module Boolean where

open import Cubical.Data.Nat
open import Cubical.Core.Everything
open import Cubical.Foundations.Isomorphism
open import Cubical.Relation.Nullary
open import Data.Vec
open import Data.List
open import Data.Fin renaming (_+_ to _Fin+_)
open import Function
open import Data.Nat.DivMod
import Relation.Binary.PropositionalEquality as P
open import Cubical.Induction.WellFounded

data 𝔹 : Set where
  0B : 𝔹
  1B : 𝔹

infixl 20 _AND_
infixl 10 _OR_
infixl 30 NOT_

Binary : ℕ → Set
Binary n = Vec 𝔹 n

_AND_ : 𝔹 → 𝔹 → 𝔹
0B AND y = 0B
1B AND y = y

_OR_ : 𝔹 → 𝔹 → 𝔹
0B OR y = y
1B OR y = 1B

NOT_ : 𝔹 → 𝔹
NOT 0B = 1B
NOT 1B = 0B

_XOR_ : 𝔹 → 𝔹 → 𝔹
a XOR b = a AND NOT b OR NOT a AND b

discrete𝔹 : Discrete 𝔹
discrete𝔹 0B 0B = yes refl
discrete𝔹 0B 1B = no {!   !}
discrete𝔹 1B 0B = no {!   !}
discrete𝔹 1B 1B = yes refl

HA : 𝔹 → 𝔹 → Binary 2
HA a b = a AND b ∷ a XOR b ∷ []

FA : 𝔹 → 𝔹 → 𝔹 → Binary 2
FA a b c = case (HA a b) of λ {(c₀ ∷ s₀ ∷ []) → case (HA c s₀) of λ {(c₁ ∷ s ∷ []) → (c₁ OR c₀) ∷ s ∷ []}}

-- weakCanonicity : (b : 𝔹) → b ≡ 0B ⊎ b ≡ 1B
-- weakCanonicity b = ?

rightSucExpand : ∀ m n → m + suc n ≡ suc (m + n)
rightSucExpand zero n = refl
rightSucExpand (suc m) n = cong suc (rightSucExpand m n)

𝔹toℕ : 𝔹 → ℕ
𝔹toℕ 0B = 0
𝔹toℕ 1B = 1

𝔹toFin : 𝔹 → Fin 2
𝔹toFin 0B = zero
𝔹toFin 1B = suc zero

Finto𝔹 : Fin 2 → 𝔹
Finto𝔹 zero = 0B
Finto𝔹 (suc zero) = 1B

_lossy+_ : {m n : ℕ} → Fin (suc m) → Fin (suc n) → Fin (suc (m + n))
_lossy+_ {m} {n} zero b = subst Fin (rightSucExpand m n) (raise m b)
_lossy+_ {zero} {n} (suc ()) b
_lossy+_ {suc m} {n} (suc a) b = Fin.suc (a lossy+ b)

_Fin*_ : {m n : ℕ} → Fin (suc m) → Fin (suc n) → Fin (suc (m * n))
_Fin*_ {m} {n} zero b = zero
_Fin*_ {zero} {n} (suc ()) b
_Fin*_ {suc m} {n} (suc a) b = b lossy+ (a Fin* b)
-- b Fin+ (a Fin* b)

_^_ : ℕ → ℕ → ℕ
a ^ zero = 1
a ^ suc b = a * (a ^ b)

toFrom : ∀ x → toℕ (fromℕ x) ≡ x
toFrom zero = refl
toFrom (suc x) = cong suc (toFrom x)

binToℕ : {n : ℕ} → Binary (suc n) → ℕ
binToℕ {zero} (x ∷ []) = 𝔹toℕ x
binToℕ {suc n} (x ∷ xs) = doublesℕ (suc n) (𝔹toℕ x) + binToℕ xs

-- ℕToBin : (n : ℕ) → List 𝔹
-- ℕToBin zero = 0B ∷ []
-- ℕToBin (suc zero) = 1B ∷ []
-- ℕToBin n = case (discreteℕ (n % 2) 0) of λ { (yes _) → 1B ∷ ℕToBin (n div 2) ; (no _) → 0B ∷ ℕToBin (n div 2) }

binToFinFold : {n : ℕ} → Binary (suc n) → Fin (2 ^ (suc n))
binToFinFold (x ∷ []) = 𝔹toFin x
binToFinFold {suc n} (0B ∷ xs) = subst Fin (f n) (raise ((2 ^ n) + (2 ^ n)) (binToFinFold xs))
  where f : ∀ n → (2 ^ n) + (2 ^ n) + ((2 ^ n) + ((2 ^ n) + zero)) ≡ (2 ^ n) + ((2 ^ n) + zero) + ((2 ^ n) + ((2 ^ n) + zero) + zero)
        f n = sym $
          (2 ^ n) + ((2 ^ n) + zero) + ((2 ^ n) + ((2 ^ n) + zero) + zero) ≡⟨ (λ i → (2 ^ n) + (+-zero (2 ^ n) i) + (+-zero ((2 ^ n) + (+-zero (2 ^ n) i)) i)) ⟩
          (2 ^ n) + (2 ^ n) + ((2 ^ n) + (2 ^ n)) ≡⟨ (λ i → (2 ^ n) + (2 ^ n) + ((2 ^ n) + +-zero (2 ^ n) (~ i))) ⟩
          (2 ^ n) + (2 ^ n) + ((2 ^ n) + ((2 ^ n) + zero)) ∎
binToFinFold {suc n} (1B ∷ xs) = subst Fin (f n) (raise (2 ^ n) (fromℕ (2 ^ n) Fin+ binToFinFold xs))
  where f : ∀ n → (2 ^ n) + (toℕ (fromℕ (2 ^ n)) + ((2 ^ n) + ((2 ^ n) + zero))) ≡ (2 ^ n) + ((2 ^ n) + zero) + ((2 ^ n) + ((2 ^ n) + zero) + zero)
        f n =
          (2 ^ n) + (toℕ (fromℕ (2 ^ n)) + ((2 ^ n) + ((2 ^ n) + zero))) ≡⟨ (λ i → (2 ^ n) + (toFrom (2 ^ n) i + ((2 ^ n) + (+-zero (2 ^ n) i)))) ⟩
          (2 ^ n) + ((2 ^ n) + ((2 ^ n) + (2 ^ n))) ≡⟨ (λ i → +-assoc (2 ^ n) (+-zero (2 ^ n) (~ i)) (+-zero ((2 ^ n) + (+-zero (2 ^ n) (~ i))) (~ i)) i) ⟩
          (2 ^ n) + ((2 ^ n) + zero) + ((2 ^ n) + ((2 ^ n) + zero) + zero) ∎
-- binToFinFold {suc n} (x ∷ xs) = raise {!  !} (subst Fin (f n) (((fromℕ (2 ^ n) Fin* (𝔹toFin x)) Fin+ (binToFinFold xs))))
--   where f : (n : ℕ) → toℕ (fromℕ (2 ^ n) Fin* 𝔹toFin x) + ((2 ^ n) + ((2 ^ n) + zero)) ≡ {!   !}
--         f n = {!   !}

power2Reduction : {n : ℕ} → Fin (2 ^ (suc n)) → Σ (Fin (2 ^ n)) (λ _ → 𝔹)
power2Reduction {zero} zero = zero , 0B
power2Reduction {zero} (suc zero) = zero , 1B
power2Reduction {zero} (suc (suc ()))
power2Reduction {suc n} x = let res = (toℕ x) divMod 2 in inject≤ (fromℕ (DivMod.quotient res)) {!   !} , Finto𝔹 (DivMod.remainder res)

finToBin : {n : ℕ} → Fin (2 ^ (suc n)) → Binary (suc n)
finToBin {zero} zero = 0B ∷ []
finToBin {zero} (suc zero) = 1B ∷ []
finToBin {zero} (suc (suc ()))
finToBin {suc n} x = (case discreteℕ (toℕ x % 2) 0 of λ { (yes _) → 1B ; (no _) → 0B }) ∷ {! finToBin (fromℕ (toℕ x div 2))  !}

binEqualFin : {n : ℕ} → Binary (suc n) ≡ Fin (2 ^ (suc n))
binEqualFin = isoToPath (iso binToFinFold finToBin {!   !} {!   !})

-- Carry ripple, carry save
