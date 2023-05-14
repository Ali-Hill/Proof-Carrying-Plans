module Naughty.naughty where

open import Relation.Binary.PropositionalEquality
open import Relation.Binary
open import Data.List
open import Data.List.Relation.Unary.Any
open import Relation.Nullary using (yes; no; Dec)
open import Level
open import Data.Product
open import Tactic.Deriving.Eq

data C : Set where
 a b c d e f1 : C
-- EqC : Eq C
unquoteDecl EqC = deriveEq EqC (quote C)

data Predicate : Set where
  handEmpty : Predicate
-- EqR : Eq Predictate
unquoteDecl EqR = deriveEq EqR (quote Predicate)

data Action : Set where
  naughty : Action
-- EqAction : Eq Action
unquoteDecl EqAction = deriveEq EqAction (quote Action)
open import Plans.Domain.Core Action Predicate

Γ : Context
Γ (naughty) = record {
  preconditions = [] ;
  effects = (+ , handEmpty) ∷ (- , handEmpty) ∷ []}

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
