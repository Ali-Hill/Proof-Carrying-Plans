open import blocksworldDomain
open import Plans.Semantics blocksworldWDomain
open import Plans.PlanW blocksworldWDomain
open import Data.List
open import Data.Product renaming (_,_ to _↝_)
open import Relation.Nullary.Decidable

module blocksworldExample where

open import Data.Nat
open import Agda.Builtin.FromNat
open import Data.Fin
import Data.Nat.Literals as NatLiterals
import Data.Fin.Literals as FinLiterals
open import Data.Unit
open import Universal.blocksworldActionHandler
open import Data.Maybe

instance
  NumNat : Number ℕ
  NumNat = NatLiterals.number

instance
  NumFin : ∀ {n} → Number (Fin n)
  NumFin {n} = FinLiterals.number n

-- Recover object names using pattern synonyms
a = obj 0
b = obj 1
c = obj 2
d = obj 3
e = obj 4
f = obj 5

P : World
P = (ontable a) ∷ (ontable b) ∷ (ontable c) ∷ (ontable d) ∷ (ontable e) ∷ (ontable f) ∷ (clear a) ∷ (clear b) ∷ (clear c) ∷ (clear d) ∷ (clear e) ∷ (clear f) ∷ (handempty) ∷ []

Q : State
Q = (+ ↝ (on a b)) ∷ (+ ↝ (on b c)) ∷ (+ ↝ (on c d)) ∷ (+ ↝ (on d e)) ∷ (+ ↝ (on e f)) ∷ []

plan : Plan
plan = pickup_from_table e ∷ putdown_on_stack e f ∷ pickup_from_table d ∷ putdown_on_stack d e ∷ pickup_from_table c ∷ putdown_on_stack c d ∷ pickup_from_table b ∷ putdown_on_stack b c ∷ pickup_from_table a ∷ putdown_on_stack a b ∷ halt

Derivation : Γ ⊢ plan ∶ P ↝ Q 
Derivation = from-yes (solver Γ plan P Q)

testEvaluation : Maybe correctWorld
testEvaluation = executeWorld plan (enriched-σ Γ) P
