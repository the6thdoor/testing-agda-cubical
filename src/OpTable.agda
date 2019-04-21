{-# OPTIONS --cubical --safe #-}
module OpTable where

open import Cubical.Core.Everything
open import Cubical.Data.Nat
open import AbstractAlgebra
open import Data.Vec
open import Data.Fin
open import Data.Product
open import Function
open import Data.Nat.DivMod

-- OpTable is an operation table corresponding to a finite binary operation ∘ : G → G → G, where G is a FINITE group.

data OpMapping : Set → Set₁ where
  _,_↦_ : {G : Set} → G → G → G → OpMapping G

OpTable : (G : Set) (n : ℕ) → Set₁
OpTable G n = Vec (OpMapping G) n

two : OpTable (Fin 2) 4
two = (zero , zero ↦ zero) ∷ (zero , (suc zero) ↦ (suc zero)) ∷ ((suc zero) , zero ↦ (suc zero)) ∷ ((suc zero) , (suc zero) ↦ zero) ∷ []

lkp : {A : Set} {n : ℕ} → OpTable A n → A → A → A
lkp tbl a b = {!   !}

equivFunction : OpTable (Fin 2) 4 ≡ {!   !} -- a complete OpTable on Fin 2 corresponds to a total function f : Fin 2 → Fin 2
equivFunction = {!   !}

genFinTable : (n : ℕ) → (f : Fin n → Fin n → Fin n) → Vec ((Fin n × Fin n) × Fin n) (n * n)
genFinTable n f = Data.Vec.map (λ x → x , (f (fst x) (snd x))) (allPairs (allFin n) (allFin n))

exTable : Vec ((Fin 5 × Fin 5) × Fin 5) 25
exTable = genFinTable 5 λ x y → x

tblFinToℕ : {n : ℕ} → Vec ((Fin n × Fin n) × Fin n) (n * n) → Vec ((ℕ × ℕ) × ℕ) (n * n)
tblFinToℕ tbl = Data.Vec.map (λ x → Data.Product.map toℕ toℕ (fst x) , toℕ (snd x)) tbl

addModN : (n : ℕ) → Fin n → Fin n → Fin n
addModN n x y = ((toℕ x) Cubical.Data.Nat.+ (toℕ y)) mod n

tblLookup : {m n : ℕ} {A B C : Set} → Vec ((A × B) × C) (m * n) → A → B → C
tblLookup tbl a b = {! fiber  !}
