module test where

open import Relation.Binary.PropositionalEquality
open import Relation.Binary
open import Data.List
open import Data.List.Relation.Unary.Any
open import Relation.Nullary using (yes; no; Dec)
open import Level
open import Tactic.Deriving.Eq

data C : Set where
 taxi1 taxi2 taxi3 person1 person2 person3 location1 location2 location3 : C
-- EqC : Eq C
unquoteDecl EqC = deriveEq EqC (quote C)

data R : Set where
  isin : C → C → R
  location : C → R
  person : C → R
  taxi : C → R
-- EqR : Eq R
unquoteDecl EqR = deriveEq EqR (quote R)

data Action : Set where
  drivepassenger : C → C → C → C → Action
  drive : C → C → C → Action
-- EqAction : Eq Action
unquoteDecl EqAction = deriveEq EqAction (quote Action)

open import Mangle using (mangle)

isDecidable : IsDecEquivalence {zero} {zero} (_≡_ {A = R})
isDecidable = record { isEquivalence = record {
  refl = λ {x} → refl ;
  sym = λ x → sym x ;
  trans = trans } ;
 _≟_ = mangle  }

isDEC : IsDecEquivalence {zero} {zero} (_≡_ {A = C})
isDEC = record { isEquivalence = record {
  refl = λ {x} → refl ;
  sym = λ x → sym x ;
  trans = trans } ;
  _≟_ = mangle  }

isDECA : IsDecEquivalence {zero} {zero} (_≡_ {A = Action})
isDECA = record { isEquivalence = record {
  refl = λ {x} → refl ;
  sym = λ x → sym x ;
  trans = trans } ;
  _≟_ = mangle  }

open import PCPLogic_no_equality {Action} {R} {C} {isDecidable} {isDEC} {isDECA}

open import Data.Product

Γ₁ : Γ
Γ₁ (drivepassenger t1 p1 l1 l2) = (+ , isin t1 l1) ∷ (+ , isin p1 l1) ∷ [] , (- , isin t1 l1) ∷ (- , isin p1 l1) ∷ (+ , isin t1 l2) ∷ (+ , isin p1 l2) ∷ []
Γ₁ (drive t1 l1 l2) = (+ , isin t1 l1) ∷ [] , (+ , isin t1 l1) ∷ []

open Data.Product renaming (_,_ to _↝_)


P : State
P = (+ ↝ (isin taxi1 location1)) ∷ (+ ↝ (isin taxi2 location2)) ∷ (+ ↝ (isin taxi3 location3)) ∷ (+ ↝ (isin person1 location1)) ∷ (+ ↝ (isin person2 location2)) ∷ (+ ↝ (isin person3 location3)) ∷ []

Q : State
Q = (+ ↝ (isin taxi1 location2)) ∷ (+ ↝ (isin person1 location3)) ∷ (+ ↝ (isin person3 location1)) ∷ []

open import Relation.Nullary.Decidable
open import Data.Unit
