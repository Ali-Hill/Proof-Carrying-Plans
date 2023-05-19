open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Data.Product
open import Data.List hiding (any)
open import Relation.Nullary
open import AnyLemma

module ActionHandler {Action : Set} {R : Set} {C : Set} {isDE : IsDecEquivalence {A = R} (_≡_) }
                                              {isDEC : IsDecEquivalence {A = C} (_≡_) }
                                              {isDECA : IsDecEquivalence {A = Action} (_≡_) }  where


open import Grammar {Action} {R} {C} 
open import Membership_And_State {Action} {R} {C} {isDE} {isDEC} {isDECA}
open import Subtyping PredMap isSame
                                              
-- Action Handler
ActionHandler : Set
ActionHandler = Action → World → World

-- Evaluation function
⟦_⟧ : f → ActionHandler → World → World
⟦ shrink ⟧ σ w = w
⟦ act x ⟧ σ w = σ x w
⟦ join x x₁ ⟧ σ w = ⟦ x₁ ⟧ σ (⟦ x ⟧ σ w) --first actions in x

open IsDecEquivalence isDE

del : R → State → State
del x [] = []
del x ((z , a) ∷ S) with x ≟ a
del x ((z , a) ∷ S) | yes p =  del x S
del x ((z , a) ∷ S) | no ¬p = (z , a) ∷ del x S

-- Override operator
_⊔N_ : State → State → State
P ⊔N [] = P
P ⊔N ((z , a) ∷ Q) = (z , a) ∷ del a P ⊔N Q

-- Well formed handler

{-
  If we have an action α in gamma
  And has preconditions proj₁ (Γ α) and postconditions proj₂ (Γ α)
  proj₁ (Γ α) is a subtype of M
  and M is true in the world w
  then the application of the action handler σ of action α
  results in M being overriden by proj₂ (Γ α) in w
-}

WfHandler : Γ → ActionHandler → Set
WfHandler Γ σ =
  ∀{α P} → proj₁ (Γ α) <: P → ∀{w} → w ∈⟨ P ⟩ → σ α w ∈⟨ P ⊔N proj₂ (Γ α) ⟩

open import Expressions {Action} {R} {C} {isDEC}

-- Well formed handler for expressions

open ActionDescription

WfHandlerₑ : Γₑ → ActionHandler → Set
WfHandlerₑ Γₑ σ =
  ∀{α P w} → P <: (preconditions (Γₑ α))
           → w ∈⟨ P ⟩
           → trueListExp (expressions (Γₑ α))
           → ValidState (postconditions (Γₑ α))
           → σ α w ∈⟨ P ⊔N (postconditions (Γₑ α)) ⟩
