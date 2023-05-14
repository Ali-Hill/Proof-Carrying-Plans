module mprime where

open import Relation.Binary.PropositionalEquality
open import Relation.Binary
open import Data.List
open import Data.List.Relation.Unary.Any
open import Relation.Nullary using (yes; no; Dec)
open import Level
open import Tactic.Deriving.Eq

data C : Set where
 muffin ham scallion shrimp cherry grapefruit bacon arugula scallop wurst aesthetics hangover dread sciatica jealousy loneliness abrasion anger surrey quebec bosnia oregon kentucky mars vulcan : C
-- EqC : Eq C
unquoteDecl EqC = deriveEq EqC (quote C)

data R : Set where
  orbits : C → C → R
  attacks : C → C → R
  harmony : C → C → R
  locale : C → C → R
  fears : C → C → R
  craves : C → C → R
  eats : C → C → R
  pain : C → R
  pleasure : C → R
  food : C → R
  planet : C → R
  province : C → R
-- EqR : Eq R
unquoteDecl EqR = deriveEq EqR (quote R)

data Action : Set where
  overcome : C → C → C → C → C → Action
  feast : C → C → C → C → C → Action
  succumb : C → C → C → C → C → Action
  drink : C → C → C → C → C → C → C → Action
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

open import PCPLogic {Action} {R} {C} {isDecidable} {isDEC} {isDECA}
open import Grammar {Action} {R} {C}
open import Membership_And_State {Action} {R} {C} {isDecidable} {isDEC} {isDECA}
open import Subtyping PredMap isSame
open import Proofs.Consistency {Action} {R} {C} {isDecidable} {isDEC} {isDECA}

open import Data.Product

Γ₁ : Γₑ
Γ₁ (overcome c v n s1 s2) = record { expressions = []  ; preconditions = (+ , pain c) ∷ (+ , pleasure v) ∷ (+ , craves c n) ∷ (+ , craves v n) ∷ (+ , food n) ∷ (+ , harmony v s2) ∷ (+ , planet s2) ∷ (+ , orbits s1 s2) ∷ (+ , planet s1) ∷ [] ; postconditions = (+ , planet s1) ∷ (+ , orbits s1 s2) ∷ (+ , planet s2) ∷ (+ , food n) ∷ (+ , craves v n) ∷ (+ , pleasure v) ∷ (+ , pain c) ∷ (- , craves c n) ∷ (+ , fears c v) ∷ (- , harmony v s2) ∷ (+ , harmony v s1) ∷ [] }
Γ₁ (feast v n1 n2 l1 l2) = record { expressions = []  ; preconditions = (+ , craves v n1) ∷ (+ , food n1) ∷ (+ , pleasure v) ∷ (+ , eats n1 n2) ∷ (+ , food n2) ∷ (+ , locale n1 l2) ∷ (+ , attacks l1 l2) ∷ [] ; postconditions = (+ , attacks l1 l2) ∷ (+ , food n2) ∷ (+ , eats n1 n2) ∷ (+ , pleasure v) ∷ (+ , food n1) ∷ (- , craves v n1) ∷ (+ , craves v n2) ∷ (- , locale n1 l2) ∷ (+ , locale n1 l1) ∷ [] }
Γ₁ (succumb c v n s1 s2) = record { expressions = []  ; preconditions = (+ , fears c v) ∷ (+ , pain c) ∷ (+ , pleasure v) ∷ (+ , craves v n) ∷ (+ , food n) ∷ (+ , harmony v s1) ∷ (+ , orbits s1 s2) ∷ [] ; postconditions = (+ , orbits s1 s2) ∷ (+ , food n) ∷ (+ , craves v n) ∷ (+ , pleasure v) ∷ (+ , pain c) ∷ (- , fears c v) ∷ (+ , craves c n) ∷ (- , harmony v s1) ∷ (+ , harmony v s2) ∷ [] }
Γ₁ (drink n1 n2 l11 l12 l13 l21 l22) = record { expressions = n1 ¬L n2 ∷ []  ; preconditions = (+ , locale n1 l11) ∷ (+ , attacks l12 l11) ∷ (+ , attacks l13 l12) ∷ (+ , locale n2 l21) ∷ (+ , attacks l21 l22) ∷ [] ; postconditions = (+ , attacks l21 l22) ∷ (+ , attacks l13 l12) ∷ (+ , attacks l12 l11) ∷ (- , locale n1 l11) ∷ (+ , locale n1 l12) ∷ (- , locale n2 l21) ∷ (+ , locale n2 l22) ∷ [] }

open Data.Product renaming (_,_ to _↝_)


P : State
P = (+ ↝ (food muffin)) ∷ (+ ↝ (food ham)) ∷ (+ ↝ (food scallion)) ∷ (+ ↝ (food shrimp)) ∷ (+ ↝ (food cherry)) ∷ (+ ↝ (food grapefruit)) ∷ (+ ↝ (food bacon)) ∷ (+ ↝ (food arugula)) ∷ (+ ↝ (food scallop)) ∷ (+ ↝ (food wurst)) ∷ (+ ↝ (pleasure aesthetics)) ∷ (+ ↝ (pain hangover)) ∷ (+ ↝ (pain dread)) ∷ (+ ↝ (pain sciatica)) ∷ (+ ↝ (pain jealousy)) ∷ (+ ↝ (pain loneliness)) ∷ (+ ↝ (pain abrasion)) ∷ (+ ↝ (pain anger)) ∷ (+ ↝ (province surrey)) ∷ (+ ↝ (province quebec)) ∷ (+ ↝ (province bosnia)) ∷ (+ ↝ (province oregon)) ∷ (+ ↝ (province kentucky)) ∷ (+ ↝ (planet mars)) ∷ (+ ↝ (planet vulcan)) ∷ (+ ↝ (locale cherry kentucky)) ∷ (+ ↝ (eats ham muffin)) ∷ (+ ↝ (eats cherry shrimp)) ∷ (+ ↝ (locale scallion quebec)) ∷ (+ ↝ (craves dread ham)) ∷ (+ ↝ (eats cherry ham)) ∷ (+ ↝ (eats grapefruit scallop)) ∷ (+ ↝ (craves sciatica grapefruit)) ∷ (+ ↝ (eats wurst bacon)) ∷ (+ ↝ (eats muffin ham)) ∷ (+ ↝ (attacks oregon kentucky)) ∷ (+ ↝ (eats arugula scallop)) ∷ (+ ↝ (eats arugula bacon)) ∷ (+ ↝ (eats bacon wurst)) ∷ (+ ↝ (eats arugula muffin)) ∷ (+ ↝ (craves anger wurst)) ∷ (+ ↝ (eats scallion shrimp)) ∷ (+ ↝ (eats arugula wurst)) ∷ (+ ↝ (locale arugula kentucky)) ∷ (+ ↝ (eats grapefruit wurst)) ∷ (+ ↝ (craves loneliness arugula)) ∷ (+ ↝ (harmony aesthetics vulcan)) ∷ (+ ↝ (eats muffin cherry)) ∷ (+ ↝ (eats scallop arugula)) ∷ (+ ↝ (locale muffin kentucky)) ∷ (+ ↝ (locale grapefruit surrey)) ∷ (+ ↝ (craves hangover muffin)) ∷ (+ ↝ (eats cherry arugula)) ∷ (+ ↝ (eats shrimp scallion)) ∷ (+ ↝ (locale ham bosnia)) ∷ (+ ↝ (eats muffin scallion)) ∷ (+ ↝ (eats arugula cherry)) ∷ (+ ↝ (eats scallop grapefruit)) ∷ (+ ↝ (craves abrasion scallop)) ∷ (+ ↝ (eats bacon arugula)) ∷ (+ ↝ (eats ham cherry)) ∷ (+ ↝ (eats cherry muffin)) ∷ (+ ↝ (locale bacon quebec)) ∷ (+ ↝ (locale wurst surrey)) ∷ (+ ↝ (attacks bosnia oregon)) ∷ (+ ↝ (locale scallop oregon)) ∷ (+ ↝ (eats shrimp cherry)) ∷ (+ ↝ (eats wurst arugula)) ∷ (+ ↝ (attacks quebec bosnia)) ∷ (+ ↝ (eats muffin arugula)) ∷ (+ ↝ (attacks surrey quebec)) ∷ (+ ↝ (craves aesthetics shrimp)) ∷ (+ ↝ (eats scallion muffin)) ∷ (+ ↝ (orbits mars vulcan)) ∷ (+ ↝ (locale shrimp bosnia)) ∷ (+ ↝ (craves jealousy bacon)) ∷ (+ ↝ (eats wurst grapefruit)) ∷ []

Q : State
Q = (+ ↝ (craves sciatica wurst)) ∷ []

open import Relation.Nullary.Decidable
open import Data.Unit
