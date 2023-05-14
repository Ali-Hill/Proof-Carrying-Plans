module test where

open import Relation.Binary.PropositionalEquality
open import Relation.Binary
open import Data.List
open import Data.List.Relation.Unary.Any
open import Relation.Nullary using (yes; no; Dec)
open import Level
open import Tactic.Deriving.Eq

data C : Set where
 a b c d e f1 : C
-- EqC : Eq C
unquoteDecl EqC = deriveEq EqC (quote C)

data R : Set where
  clear : C → R
  on : C → C → R
  ontable : C → R
  holding : C → R
  handempty : R
-- EqR : Eq R
unquoteDecl EqR = deriveEq EqR (quote R)

data Action : Set where
  pickup_from_table : C → Action
  putdown_on_table : C → Action
  pickup_from_stack : C → C → Action
  putdown_on_stack : C → C → Action
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
Γ₁ (pickup_from_table x) = (+ , handempty) ∷ (+ , ontable x) ∷ (+ , clear x) ∷ [] , (+ , clear x) ∷ (- , handempty) ∷ (- , ontable x) ∷ (+ , holding x) ∷ []
Γ₁ (putdown_on_table x) = (+ , holding x) ∷ [] , (- , holding x) ∷ (+ , ontable x) ∷ (+ , handempty) ∷ []
Γ₁ (pickup_from_stack x y) = (+ , on x y) ∷ (+ , clear x) ∷ (+ , handempty) ∷ [] , (+ , clear x) ∷ (- , on x y) ∷ (- , handempty) ∷ (+ , holding x) ∷ (+ , clear y) ∷ []
Γ₁ (putdown_on_stack x y) = (+ , holding x) ∷ (+ , clear y) ∷ [] , (- , holding x) ∷ (- , clear y) ∷ (+ , on x y) ∷ (+ , handempty) ∷ []

open Data.Product renaming (_,_ to _↝_)


P : State
P = (+ ↝ (ontable a)) ∷ (+ ↝ (ontable b)) ∷ (+ ↝ (ontable c)) ∷ (+ ↝ (ontable d)) ∷ (+ ↝ (ontable e)) ∷ (+ ↝ (ontable f1)) ∷ (+ ↝ (clear a)) ∷ (+ ↝ (clear b)) ∷ (+ ↝ (clear c)) ∷ (+ ↝ (clear d)) ∷ (+ ↝ (clear e)) ∷ (+ ↝ (clear f1)) ∷ (+ ↝ (handempty)) ∷ []

Q : State
Q = (+ ↝ (on a b)) ∷ (+ ↝ (on b c)) ∷ (+ ↝ (on c d)) ∷ (+ ↝ (on d e)) ∷ (+ ↝ (on e f1)) ∷ []

open import Relation.Nullary.Decidable
open import Data.Unit
