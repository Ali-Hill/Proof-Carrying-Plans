module Blocksworld.Blocksworld where

open import Relation.Binary.PropositionalEquality
open import Relation.Binary
open import Data.List
open import Data.List.Relation.Unary.Any
open import Relation.Nullary using (yes; no; Dec)
open import Level
open import Tactic.Deriving.Eq
open import Data.Product

data Object : Set where
 a b c : Object
-- EqC : Eq C
unquoteDecl EqC = deriveEq EqC (quote Object)

data Predicate : Set where
  clear : Object → Predicate
  on : Object → Object → Predicate
  onTable : Object → Predicate
  holding : Object → Predicate
  handEmpty : Predicate
 -- EqR : Eq R
unquoteDecl EqR = deriveEq EqR (quote Predicate)

data Action : Set where
  pickup_from_table :
    Object → Action
  putdown_on_table  : 
    Object → Action
  pickup_from_stack :
    Object → Object → Action
  putdown_on_stack  :
    Object → Object → Action
-- EqAction : Eq Action
unquoteDecl EqAction = deriveEq EqAction (quote Action)

open import Plans.Domain.Core Action Predicate

Γ : Context
Γ (pickup_from_table x) = record {
  preconditions =
    (+ , handEmpty) ∷
    (+ , onTable x) ∷
    (+ , clear x) ∷ [] ;
  effects =
    (+ , clear x) ∷
    (- , handEmpty) ∷
    (- , onTable x) ∷
    (+ , holding x) ∷ [] }
Γ (putdown_on_table x) = record {
  preconditions = (+ , holding x) ∷ [] ;
  effects = (- , holding x) ∷ (+ , onTable x) ∷ (+ , handEmpty) ∷ [] }
Γ (pickup_from_stack x y) = record {
  preconditions = (+ , on x y) ∷ (+ , clear x) ∷ (+ , handEmpty) ∷ [] ;
  effects = (+ , clear x) ∷ (- , on x y) ∷ (- , handEmpty) ∷ (+ , holding x) ∷ (+ , clear y) ∷ [] }
Γ (putdown_on_stack x y) = record {
  preconditions = (+ , holding x) ∷ (+ , clear y) ∷ [] ;
  effects = (- , holding x) ∷ (- , clear y) ∷ (+ , on x y) ∷ (+ , handEmpty) ∷ [] }

open import Plans.Mangle using (mangle)
open import Plans.Domain
open import Plans.Domain.Core

blocksworldDomain : Domain
blocksworldDomain = record
  { Predicate = Predicate
  ; Action = Action
  ; Γ = Γ
  ; _≟ₚ_ = mangle }

open Domain blocksworldDomain  public
  hiding (Action; Predicate; Γ)
