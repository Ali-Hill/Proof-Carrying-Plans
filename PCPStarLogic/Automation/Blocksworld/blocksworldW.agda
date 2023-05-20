module blocksworldW where

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
open import Plans.Domain.Core Action R

Γ : Context
Γ (pickup_from_table x) = record { preconditions =(+ , handempty) ∷ (+ , ontable x) ∷ (+ , clear x) ∷ [] ; effects =(+ , clear x) ∷ (- , handempty) ∷ (- , ontable x) ∷ (+ , holding x) ∷ []}
Γ (putdown_on_table x) = record { preconditions =(+ , holding x) ∷ [] ; effects =(- , holding x) ∷ (+ , ontable x) ∷ (+ , handempty) ∷ []}
Γ (pickup_from_stack x y) = record { preconditions =(+ , on x y) ∷ (+ , clear x) ∷ (+ , handempty) ∷ [] ; effects =(+ , clear x) ∷ (- , on x y) ∷ (- , handempty) ∷ (+ , holding x) ∷ (+ , clear y) ∷ []}
Γ (putdown_on_stack x y) = record { preconditions =(+ , holding x) ∷ (+ , clear y) ∷ [] ; effects =(- , holding x) ∷ (- , clear y) ∷ (+ , on x y) ∷ (+ , handempty) ∷ []}

open import Plans.Mangle using (mangle)
open import Plans.Domain
open import Plans.Domain.Core

blocksworldWDomain : Domain
blocksworldWDomain = record
  { Predicate = R
  ; Action = Action
  ; Γ = Γ
  ; _≟ₚ_ = mangle }

open Domain blocksworldWDomain  public
  hiding (Action; Predicate; Γ)
