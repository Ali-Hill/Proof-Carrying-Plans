module blocksworldDomain where

open import Relation.Binary.PropositionalEquality
open import Relation.Binary
open import Data.List
open import Data.List.Relation.Unary.Any
open import Relation.Nullary using (yes; no; Dec)
open import Level
open import Data.Product
open import Tactic.Deriving.Eq

open import Data.Nat hiding (_≟_)
open import Data.Fin

open import Data.Fin.Properties using (_≟_)

open import Plans.Mangle using (mangle; mangle')

objects : ℕ
objects = 6

data Object : Set where
 obj : Fin objects → Object

Object? : DecidableEquality Object
Object? (obj x) (obj x₁) with x ≟ x₁
... | no ¬p = no (λ { refl → ¬p refl})
... | yes refl = yes refl

instance
  _ = mangle' Object?

data Predicate : Set where
  clear : Object → Predicate
  on : Object → Object → Predicate
  ontable : Object → Predicate
  holding : Object → Predicate
  handempty : Predicate
-- EqPredicate : Eq Predicate
unquoteDecl EqPredicate = deriveEq EqPredicate (quote Predicate)

data Action : Set where
  pickup_from_table : Object → Action
  putdown_on_table : Object → Action
  pickup_from_stack : Object → Object → Action
  putdown_on_stack : Object → Object → Action
-- EqAction : Eq Action
unquoteDecl EqAction = deriveEq EqAction (quote Action)

open import Plans.Domain.Core Action Predicate

Γ : Context
Γ (pickup_from_table x) = record { preconditions =(+ , handempty) ∷ (+ , ontable x) ∷ (+ , clear x) ∷ [] ; effects =(+ , clear x) ∷ (- , handempty) ∷ (- , ontable x) ∷ (+ , holding x) ∷ []}
Γ (putdown_on_table x) = record { preconditions =(+ , holding x) ∷ [] ; effects =(- , holding x) ∷ (+ , ontable x) ∷ (+ , handempty) ∷ []}
Γ (pickup_from_stack x y) = record { preconditions =(+ , on x y) ∷ (+ , clear x) ∷ (+ , handempty) ∷ [] ; effects =(+ , clear x) ∷ (- , on x y) ∷ (- , handempty) ∷ (+ , holding x) ∷ (+ , clear y) ∷ []}
Γ (putdown_on_stack x y) = record { preconditions =(+ , holding x) ∷ (+ , clear y) ∷ [] ; effects =(- , holding x) ∷ (- , clear y) ∷ (+ , on x y) ∷ (+ , handempty) ∷ []}

open import Plans.Domain
open import Plans.Domain.Core

blocksworldWDomain : Domain
blocksworldWDomain = record
  { Predicate = Predicate
  ; Action = Action
  ; Γ = Γ
  ; _≟ₚ_ = mangle }

open Domain blocksworldWDomain  public
  hiding (Action; Predicate; Γ)
