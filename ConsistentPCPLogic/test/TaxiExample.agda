open import Data.Product
open import Data.Sum
open import Data.List
open import Data.Unit
open import Data.Maybe
open import Agda.Builtin.FromNat
open import TaxiDomain
open import Plans.Semantics taxiDomain
open import Plans.Plan taxiDomain
open import Plans.ActionHandler taxiDomain
open import Data.Nat
open import Data.Fin
open import Agda.Builtin.FromNat using (Number)
import Data.Nat.Literals as NatLiterals
import Data.Fin.Literals as FinLiterals
open import Plans.MembershipAndStateTyped taxiDomain
open import Relation.Nullary.Decidable

module TaxiExample where

instance
  NumNat : Number ℕ
  NumNat = NatLiterals.number
  
instance
  NumFin : ∀ {n} → Number (Fin n)
  NumFin {n} = FinLiterals.number n
  
initialState : State
initialState =
  (+ , taxiIn (taxi 0) (location 0)) ∷
  (+ , taxiIn (taxi 1) (location 1)) ∷
  (+ , taxiIn (taxi 2) (location 2)) ∷
  (+ , personIn (person 0) (location 0)) ∷
  (+ , personIn (person 1) (location 1)) ∷
  (+ , personIn (person 2) (location 2)) ∷
  []

goalState : State
goalState =
  (+ , taxiIn (taxi 0) (location 1)) ∷
  (+ , personIn (person 0) (location 2)) ∷
  (+ , personIn (person 2) (location 0)) ∷
  []

planₜ : Plan
planₜ = (drive (taxi 0) (location 0) (location 1)) ∷
        (drivePassenger (taxi 2) (person 2) (location 2) (location 0)) ∷
        (drivePassenger (taxi 2) (person 0) (location 0) (location 2)) ∷
        halt

valid = from-yes (ValidS? initialState)

Derivation : Γ ⊢ planₜ ∶ initialState ¦ valid ↝ goalState
Derivation = from-just (solver Γ planₜ initialState valid goalState)

finalState : World
finalState = execute planₜ (canonical-σ Γ) (updateWorld initialState [])

{-
Output:
  taxiIn taxi3 location3 ∷
  personIn person1 location3 ∷
  personIn person3 location1 ∷
  taxiIn taxi1 location2 ∷
  taxiIn taxi2 location2 ∷
  personIn person2 location2 ∷ []
-}

