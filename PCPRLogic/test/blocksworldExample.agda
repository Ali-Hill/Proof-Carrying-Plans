module blocksworldExample where

open import Relation.Binary.PropositionalEquality
open import Relation.Binary
open import Data.List
open import Data.List.Relation.Unary.Any
open import Relation.Nullary using (yes; no; Dec)
open import Level
open import Tactic.Deriving.Eq
open import Relation.Nullary.Decidable
open import Data.Unit

data C : Set where
 a b : C
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

open import PCPLogic {Action} {R} {C} {isDecidable} {isDEC} {isDECA}
open import Grammar {Action} {R} {C}
open import Membership_And_State {Action} {R} {C} {isDecidable} {isDEC} {isDECA}
open import Subtyping PredMap isSame
open import Proofs.Consistency {Action} {R} {C} {isDecidable} {isDEC} {isDECA}

open import Data.Product

Γ₁ : Γₑ
Γ₁ (pickup_from_table x) = record { expressions = []  ; preconditions = (+ , handempty) ∷ (+ , ontable x) ∷ (+ , clear x) ∷ [] ; postconditions = (+ , clear x) ∷ (- , handempty) ∷ (- , ontable x) ∷ (+ , holding x) ∷ [] }
Γ₁ (putdown_on_table x) = record { expressions = []  ; preconditions = (+ , holding x) ∷ [] ; postconditions = (- , holding x) ∷ (+ , ontable x) ∷ (+ , handempty) ∷ [] }
Γ₁ (pickup_from_stack x y) = record { expressions = []  ; preconditions = (+ , on x y) ∷ (+ , clear x) ∷ (+ , handempty) ∷ [] ; postconditions = (+ , clear x) ∷ (- , on x y) ∷ (- , handempty) ∷ (+ , holding x) ∷ (+ , clear y) ∷ [] }
Γ₁ (putdown_on_stack x y) = record { expressions = []  ; preconditions = (+ , holding x) ∷ (+ , clear y) ∷ [] ; postconditions = (- , holding x) ∷ (- , clear y) ∷ (+ , on x y) ∷ (+ , handempty) ∷ [] }

open Data.Product renaming (_,_ to _↝_)


P : State
P = (+ , (ontable a))
    ∷ (+ , (ontable b))
    ∷ (+ , (clear a))
    ∷ (+ , (clear b))
    ∷ (+ , (handempty)) ∷ []

Q : State
Q = (+ , (on a b)) ∷ (+ , (ontable b)) ∷ []

P' : State
P' = (+ , ontable b)
     ∷ (+ , clear b)
     ∷ (+ , handempty)
     ∷ (+ , ontable a)
     ∷ (+ , clear a) ∷ []

plan : f
plan = (join (join (act (pickup_from_table  a)) (act (putdown_on_stack  a b))) shrink)

Derivation : Γ₁ , P ↝ Q ¦ plan
Derivation = weakening P (from-yes (decSub P P')) tt (composition 
        (weakComp (from-yes
                  (decSub ((+ , ontable b)
                            ∷ (+ , clear b)
                            ∷ (+ , clear a)
                            ∷ (- , handempty)
                            ∷ (- , ontable a)
                            ∷ (+ , holding a) ∷ [])
                              ((- , ontable a)
                                ∷ (+ , ontable b)
                                ∷ (+ , clear a)
                                ∷ (+ , holding a)
                                ∷ (+ , clear b) ∷ [])))
        ((frame + (ontable b) (λ z → z) (λ z → z)
          (frame + (clear b) (λ z → z) (λ z → z) (applyAction tt tt tt))))
        ((frame - (ontable a) (λ z → z) (λ z → z)
          (frame + (ontable b) (λ z → z) (λ z → z)
          (frame + (clear a) (λ z → z) (λ z → z) (applyAction tt tt tt))))))
        (shrink tt tt (from-yes (decSub ((- , ontable a)
                                          ∷ (+ , ontable b)
                                          ∷ (+ , clear a)
                                          ∷ (- , holding a)
                                          ∷ (- , clear b)
                                          ∷ (+ , on a b)
                                          ∷ (+ , handempty) ∷ []) Q))))
