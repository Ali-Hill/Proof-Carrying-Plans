open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Level
open import Data.Vec hiding (_++_; remove)
open import Data.List hiding (any)
open import Data.Product
open import Data.Maybe
open import Relation.Nullary
open import Data.List.Membership.Propositional
open import Agda.Builtin.Unit
open import Data.Empty
open import Data.List.Relation.Unary.Any
open import Data.Sum

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

-- Proof that deleting a predicate from a state results in a valid state
delMaintainsValidity : (s : State) -> (ValidS s) -> (e : Predicate) ->  ValidS (del e s)
delMaintainsValidity [] vs e = tt
delMaintainsValidity ((t , p) ∷ s) (vp , vs) e with e ≟ₚ p
... | yes p₁ = delMaintainsValidity s vs e
... | no ¬p = (λ x → vp (del-∈S x))
    , delMaintainsValidity s vs e

-- Regains polarity information
∈STo∈ : ∀{x M} → x ∈S M -> (+ , x) ∈ M ⊎ (- , x) ∈ M
∈STo∈ {.snd} {(+ , snd) ∷ M} (here refl) = inj₁ (here refl)
∈STo∈ {.snd} {(- , snd) ∷ M} (here refl) = inj₂ (here refl)
∈STo∈ {x} {x₂ ∷ M} (there x₁) with ∈STo∈ x₁
... | inj₁ x₃ = inj₁ (there x₃)
... | inj₂ y = inj₂ (there y)


-- Proof that once a predicate has been deleted that it can no longer exist the result of the override
predicateIsDeleted : (e : PredMap) -> (s : State) -> (ValidS s) -> (es : State)  ->(ValidS (e ∷ es))
       ->  e ∈ (del (proj₂ e) s ⊔N es) -> ⊥
predicateIsDeleted (t , p) s vs es (ve , ves) mem with ⊔-union {es} {t} {p} {(del p s)} mem
... | inj₂ y = ve (membershipHelper p t es y)
... | inj₁ (fst , snd) = del-spec t p s fst


--Helper function for override maintains validity proof
overrideHelper : (e : PredMap) -> (s : State) -> (ValidS s) -> (es : State)  ->(ValidS (e ∷ es))
       ->  proj₂ e ∈S (del (proj₂ e) s ⊔N es) -> ⊥
overrideHelper e s x es x₁ x₂ with ∈STo∈ x₂
... | inj₂ y = predicateIsDeleted (- , proj₂ e) s x es x₁ y
... | inj₁ x₃ = predicateIsDeleted (+ , proj₂ e) s x es x₁ x₃


--Proof that the override operator maintains the validity of the state when given two valid states
overrideMaintainsValidity : (s : State) -> ValidS s -> (e : State) -> ValidS e -> ValidS (s ⊔N e)
overrideMaintainsValidity s vs [] ve = vs
overrideMaintainsValidity s vs (e ∷ es) (ve , ves) =
       (λ x → overrideHelper e s vs es (ve , ves) x)
       , overrideMaintainsValidity (del (proj₂ e) s) (delMaintainsValidity s vs (proj₂ e)) es ves

data _⊢_∶_¦_↝_ : Context → Plan → (S : State) → (ValidS S) -> State → Set where
  halt : ∀{Γ currentState vs  goalState} → currentState <: goalState
             → Γ ⊢ halt ∶ currentState ¦ vs ↝ goalState 
  seq : ∀{α currentState vs goalState Γ f}
      →  currentState <: preconditions (Γ α)
      -> (prf : ValidS (effects (Γ α)))
      → Γ ⊢ f ∶ currentState ⊔N effects (Γ α) ¦ overrideMaintainsValidity currentState vs (effects (Γ α)) prf ↝ goalState
      → Γ ⊢ (α ∷ f) ∶ currentState ¦ vs ↝ goalState

---------------------------------------------------------------
-- Checks if a plan is well-typed

solver : (Γ : Context) (f : Plan) (P : State) (vs : (ValidS P)) (Q : State) → Maybe (Γ ⊢ f ∶ P ¦ vs ↝ Q)
solver Γ (x ∷ f) P vs Q with P <:? (preconditions (Γ x)) 
... | no ¬p = nothing
... | yes p with ValidS? (effects (Γ x))
... | no ¬p = nothing
... | yes ve with solver Γ f (P ⊔N (effects (Γ x))) (overrideMaintainsValidity P vs (effects (Γ x)) ve) Q
... | nothing = nothing
... | just x₁ = just (seq p ve x₁)
solver Γ halt P vs Q with P <:? Q
... | no ¬p = nothing 
... | yes p = just (halt p) 

---------------------------------------------------------------
-- Evaluate a plan

execute : Plan → ActionHandler → World → World
execute (α ∷ f) σ w = execute f σ (σ α w)
execute halt σ w = w
