open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Data.List
open import Data.Product as Product
open import Data.Maybe
open import Relation.Nullary
open import Data.List.Membership.Propositional
open import Data.List.Relation.Unary.Any
open import Function.Base using (_∘_)

open import Plans.Domain

---------------------------------------------------------------
--  Definition of plans
--
-- The following module declarations allows to develop
-- the file parametrised on an abstract domain.

module Plans.PlanW (domain : Domain) where

open Domain domain
open import Plans.Semantics domain
open import Plans.ActionHandlerW domain
open ActionDescription using (preconditions; effects)
open import Data.List.Membership.DecSetoid (decSetoid _≟ₚ_) using (_∈?_)
open import Agda.Builtin.Unit


---------------------------------------------------------------
-- Plans

data Plan : Set where
  halt : Plan
  _∷_  : Action → Plan → Plan

--------------------------------------------------------------
-- Valid State

--Defining above using Any instead
_atom≡_ : (a : Predicate) (p : PredMap) -> Set
a atom≡ s = a ≡ proj₂ s

_∈S_ : (a : Predicate) (s : State) -> Set
a ∈S s = Any (a atom≡_) s
  
-- Is an atom not in a State
_∉S_ : (a : Predicate) (s : State) -> Set
a ∉S s = Relation.Nullary.¬ (a ∈S s)

ValidS : State -> Set
ValidS [] = ⊤
ValidS ((z , r) ∷ S) = r ∉S S × ValidS S


---------------------------------------------------------------
-- Well-typing relation over plans

data _⊢_∶_↝_ : Context → Plan → World → State → Set where
  halt : ∀ {Γ currentWorld  goalState}
       → currentWorld ∈⟨ goalState ⟩
       → Γ ⊢ halt ∶ currentWorld ↝ goalState
  seq : ∀ {α currentWorld goalState Γ f}
      → currentWorld  ∈⟨ preconditions (Γ α) ⟩
      → ValidS (effects (Γ α))
      → Γ ⊢ f ∶ updateWorld (effects (Γ α)) currentWorld ↝ goalState
      → Γ ⊢ (α ∷ f) ∶ currentWorld ↝ goalState
      
---------------------------------------------------------------

isInState  : (a : Predicate) -> (s : State) -> Dec (a ∈S s)
isInState a s = any? (λ x → a ≟ₚ proj₂ x) s

ValidS? : (S : State) → Dec (ValidS S)
ValidS? [] = yes tt
ValidS? (x ∷ S) with isInState (proj₂ x) S | ValidS? S
... | yes p | _ = no λ { (fst , snd) → fst p}
... | no ¬p | no ¬p₁ = no λ { (fst , snd) → ¬p₁ snd} 
... | no ¬p | yes p = yes (¬p , p) 

_∈?⟨_⟩ : Decidable _∈⟨_⟩
w ∈?⟨ [] ⟩          = yes ((λ x ()) , (λ x ()))
w ∈?⟨ (polarity , a) ∷ S ⟩ with polarity | a ∈? w | w ∈?⟨ S ⟩
... | _ | _     | no ¬p         = no (¬p ∘ Product.map (λ fst x → fst x ∘ there) (λ snd x → snd x ∘ there))
... | + | no ¬p | yes _         = no (λ z → ¬p (proj₁ z a (here refl)))
... | + | yes p | yes (pa , pb) = yes (
  (λ { a₁ (here refl) → p
     ; a₁ (there x)   → pa a₁ x
     }) ,
  (λ { a₁ (there x) (here refl) → pb a₁ x (here refl)
     ; a₁ (there x) (there x₁)  → pb a₁ x (there x₁)
     }))
... | - | yes p | yes _         = no (λ v → proj₂ v a (here refl) p)
... | - | no ¬p | yes (pa , pb) = yes (
  (λ { a₁ (there x) → pa a₁ x}) ,
  (λ { a₁ (here refl) (here refl) → ¬p (here refl)
     ; a₁ (there x)   (here refl) → pb a₁ x (here refl)
     ; a₁ (here refl) (there x₁)  → ¬p (there x₁)
     ; a₁ (there x)   (there x₁)  → pb a₁ x  (there x₁)
     }))


solver : (Γ : Context) (f : Plan) (w : World) (g : State) → Dec (Γ ⊢ f ∶ w ↝ g)
solver Γ (x ∷ f) w g with w ∈?⟨ preconditions (Γ x) ⟩ | ValidS? (effects (Γ x))
... | no ¬p | _ = no (λ { (seq x x₁ x₂) → ¬p x})
... | yes p | no ¬p = no (λ { (seq x x₁ x₂) → ¬p x₁})
... | yes p | yes p₁ with solver Γ f (updateWorld (effects (Γ x)) w) g
... | no ¬p = no (λ { (seq x x₁ x₂) → ¬p x₂})
... | yes p₂ = yes (seq p p₁ p₂)
solver Γ halt w g with w ∈?⟨ g ⟩
... | no ¬p = no (λ { (halt x) → ¬p x})
... | yes p = yes (halt p)

---------------------------------------------------------------
-- Evaluate a plan

execute : Plan → ActionHandler → World → World
execute (α ∷ f) σ w = execute f σ (σ α w)
execute halt    σ w = w
