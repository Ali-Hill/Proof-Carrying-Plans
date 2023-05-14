open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Level
open import Data.Vec hiding (_++_; remove)
open import Data.List hiding (any)
open import Data.Product
open import Data.Maybe
open import Relation.Nullary

open import Plans.Domain

--------------------------------------------------------
--  Definition of plans
--
-- The following module declarations allows to develop
-- the file parametrised on an abstract domain.

module Plans.Plan (domain : Domain) where

open Domain domain
open import Plans.Semantics domain
open import Plans.MembershipAndStateTyped domain
open import Plans.Subtyping PredMap isSame
open import Plans.ActionHandler domain
open ActionDescription using (preconditions; effects)

---------------------------------------------------------------
-- Plans

data Plan : Set where
  _∷_ : Action → Plan → Plan
  halt : Plan

---------------------------------------------------------------
-- Well-typing relation over plans

data _⊢_↝_∶_ : Context → State → State → Plan → Set where
  halt : ∀{Γ currentState  goalState} → currentState <: goalState
             → Γ ⊢ currentState ↝ goalState ∶ halt
  seq : ∀{α currentState goalState Γ f}
      →  currentState <: preconditions (Γ α)
      → Γ ⊢ currentState ⊔N effects (Γ α) ↝ goalState ∶ f
      → Γ ⊢ currentState ↝ goalState ∶ (α ∷ f)
      
---------------------------------------------------------------
-- Checks if a plan is well-typed

solver : (Γ : Context) (f : Plan) (P Q : State) → Dec (Γ ⊢ P ↝ Q ∶ f)
solver Γ (α ∷ f) P Q with P <:? (preconditions (Γ α)) 
... | no ¬p = no λ { (seq P<:Pre d) → ¬p P<:Pre}
... | yes p with solver Γ f (P ⊔N (effects (Γ α))) Q
... | no ¬p = no (λ { (seq P<:Pre d) → ¬p d})
... | yes p₁ = yes (seq p p₁)
solver Γ halt P Q with P <:? Q
... | no ¬p = no λ { (halt P<:Q) → ¬p P<:Q}
... | yes p = yes (halt p)

---------------------------------------------------------------
-- Evaluate a plan

execute : Plan → ActionHandler → World → World
execute (α ∷ f) σ w = execute f σ (σ α w)
execute halt σ w = w
