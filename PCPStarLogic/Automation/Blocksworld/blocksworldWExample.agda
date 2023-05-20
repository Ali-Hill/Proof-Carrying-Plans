open import blocksworldW
open import Plans.Semantics blocksworldWDomain
open import Plans.PlanW blocksworldWDomain
open import Data.List
open import Data.Product renaming (_,_ to _↝_)
open import Relation.Nullary.Decidable

module blocksworldWExample where

P : World
P = (ontable a) ∷ (ontable b) ∷ (ontable c) ∷ (ontable d) ∷ (ontable e) ∷ (ontable f1) ∷ (clear a) ∷ (clear b) ∷ (clear c) ∷ (clear d) ∷ (clear e) ∷ (clear f1) ∷ (handempty) ∷ []

Q : State
Q = (+ ↝ (on a b)) ∷ (+ ↝ (on b c)) ∷ (+ ↝ (on c d)) ∷ (+ ↝ (on d e)) ∷ (+ ↝ (on e f1)) ∷ []

plan : Plan
plan = pickup_from_table e ∷ putdown_on_stack e f1 ∷ pickup_from_table d ∷ putdown_on_stack d e ∷ pickup_from_table c ∷ putdown_on_stack c d ∷ pickup_from_table b ∷ putdown_on_stack b c ∷ pickup_from_table a ∷ putdown_on_stack a b ∷ halt

Derivation : Γ ⊢ plan ∶ P ↝ Q 
Derivation = from-yes (solver Γ plan P Q)
