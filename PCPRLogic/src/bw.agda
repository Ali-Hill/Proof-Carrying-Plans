module Blocksworld where

open import Relation.Binary.PropositionalEquality
open import Relation.Binary
open import Data.List
open import Data.List.Relation.Unary.Any
open import Relation.Nullary using (yes; no; Dec)
open import Level
open import Tactic.Deriving.Eq

data Object : Set where
 a b c : Object

data Predicate : Set where
  clear : Object → Predicate
  on : Object → Object → Predicate
  ontable : Object → Predicate
  holding : Object → Predicate
  handempty : Predicate

data Action : Set where
  pickup_from_table :
    Object → Action
  putdown_on_table  : 
    Object → Action
  pickup_from_stack :
    Object → Object → Action
  putdown_on_stack  :
    Object → Object → Action

Γ : Context
Γ (pickup_from_table xagda-planning.agda-lib) = record {
  preconditions =
    (+ , handempty) ∷
    (+ , ontable x) ∷
    (+ , clear x) ∷ [] ;
  effects =
    (+ , clear x) ∷
    (- , handempty) ∷
    (- , ontable x) ∷
    (+ , holding x) ∷ [] }
Γ (putdown_on_table x) = record {
  preconditions = (+ , holding x) ∷ [] ;
  effects = (- , holding x) ∷ (+ , ontable x) ∷ (+ , handempty) ∷ [] }
Γ (pickup_from_stack x y) = record {
  preconditions = (+ , on x y) ∷ (+ , clear x) ∷ (+ , handempty) ∷ [] ;
  effects = (+ , clear x) ∷ (- , on x y) ∷ (- , handempty) ∷ (+ , holding x) ∷ (+ , clear y) ∷ [] }
Γ (putdown_on_stack x y) = record {
  preconditions = (+ , holding x) ∷ (+ , clear y) ∷ [] ;
  effects = (- , holding x) ∷ (- , clear y) ∷ (+ , on x y) ∷ (+ , handempty) ∷ [] }
